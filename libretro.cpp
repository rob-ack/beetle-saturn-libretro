#include <stdarg.h>
#include <compat/msvc.h>
#include <libretro.h>
#include <rthreads/rthreads.h>
#include <string/stdstring.h>
#include <streams/file_stream.h>

#include <ctype.h>
#include <time.h>

#include "mednafen/mednafen-types.h"
#include "mednafen/git.h"
#include "mednafen/general.h"
#include "mednafen/mempatcher.h"
#ifdef NEED_DEINTERLACER
#include "mednafen/video/surface.h"
#include "mednafen/video/Deinterlacer.h"
#endif
#include "mednafen/cdrom/CDUtility.h"

#include "mednafen/ss/ss.h"
#include "mednafen/ss/cart.h"
#include "mednafen/ss/db.h"
#include "mednafen/ss/smpc.h"
#include "mednafen/ss/sound.h"

#include "libretro_cbs.h"
#include "libretro_settings.h"
#include "input.h"
#include "disc.h"


#define MEDNAFEN_CORE_NAME                   "Beetle Saturn"
#define MEDNAFEN_CORE_VERSION                "v1.25.0-UNSTABLE"
#define MEDNAFEN_CORE_VERSION_NUMERIC        0x00102403
#define MEDNAFEN_CORE_EXTENSIONS             "cue|ccd|chd|toc|m3u"
#define MEDNAFEN_CORE_TIMING_FPS             59.82
#define MEDNAFEN_CORE_GEOMETRY_BASE_W        320
#define MEDNAFEN_CORE_GEOMETRY_BASE_H        240
#define MEDNAFEN_CORE_GEOMETRY_MAX_W         704
#define MEDNAFEN_CORE_GEOMETRY_MAX_H         576
#define MEDNAFEN_CORE_GEOMETRY_ASPECT_RATIO  (4.0 / 3.0)
#define FB_WIDTH                             MEDNAFEN_CORE_GEOMETRY_MAX_W

struct retro_perf_callback perf_cb;
retro_get_cpu_features_t perf_get_cpu_features_cb = NULL;
retro_log_printf_t log_cb;
static retro_audio_sample_t audio_cb;
static retro_audio_sample_batch_t audio_batch_cb;
static retro_input_poll_t input_poll_cb;
static retro_input_state_t input_state_cb;
static retro_environment_t environ_cb;

static unsigned frame_count = 0;
static unsigned internal_frame_count = 0;
static bool failed_init = false;
static unsigned image_offset = 0;
static unsigned image_crop = 0;

static unsigned h_mask = 0;
static unsigned first_sl = 0;
static unsigned last_sl = 239;
static unsigned first_sl_pal = 0;
static unsigned last_sl_pal = 287;
bool is_pal = false;

// Sets how often (in number of output frames/retro_run invocations)
// the internal framerace counter should be updated if
// display_internal_framerate is true.
#define INTERNAL_FPS_SAMPLE_PERIOD 32

char retro_save_directory[4096];
char retro_base_directory[4096];
static char retro_cd_base_directory[4096];
static char retro_cd_path[4096];
char retro_cd_base_name[4096];

#ifndef RETRO_SLASH
#ifdef _WIN32
#define RETRO_SLASH "\\"
#else
#define RETRO_SLASH "/"
#endif
#endif

MDFNGI *MDFNGameInfo = NULL;

extern MDFNGI EmulatedSS;

// forward declarations
 bool MDFN_COLD InitCommon(const unsigned cpucache_emumode, const unsigned horrible_hacks, const unsigned cart_type, const unsigned smpc_area);
 MDFN_COLD void CloseGame(void);
 void Emulate(EmulateSpecStruct* espec_arg);

static void extract_basename(char *buf, const char *path, size_t size)
{
   const char *base = strrchr(path, '/');
   if (!base)
      base = strrchr(path, '\\');
   if (!base)
      base = path;

   if (*base == '\\' || *base == '/')
      base++;

   strncpy(buf, base, size - 1);
   buf[size - 1] = '\0';

   char *ext = strrchr(buf, '.');
   if (ext)
      *ext = '\0';
}

static void extract_directory(char *buf, const char *path, size_t size)
{
   strncpy(buf, path, size - 1);
   buf[size - 1] = '\0';

   char *base = strrchr(buf, '/');
   if (!base)
      base = strrchr(buf, '\\');

   if (base)
      *base = '\0';
   else
      buf[0] = '\0';
}

//forward decls
static bool overscan;
static double last_sound_rate;


#ifdef NEED_DEINTERLACER
static bool PrevInterlaced;
static Deinterlacer deint;
#endif

static MDFN_Surface *surf = NULL;

static void alloc_surface(void)
{
  MDFN_PixelFormat pix_fmt(MDFN_COLORSPACE_RGB, 16, 8, 0, 24);
  uint32_t width  = MEDNAFEN_CORE_GEOMETRY_MAX_W;
  uint32_t height = MEDNAFEN_CORE_GEOMETRY_MAX_H;

  if (surf != NULL)
    delete surf;

  surf = new MDFN_Surface(NULL, width, height, width, pix_fmt);
}

static void check_system_specs(void)
{
   // Hints that we need a fairly powerful system to run this.
   unsigned level = 15;
   environ_cb(RETRO_ENVIRONMENT_SET_PERFORMANCE_LEVEL, &level);
}

static void fallback_log(enum retro_log_level level, const char *fmt, ...)
{
   // stub
}

void retro_init(void)
{
   struct retro_log_callback log;

   if (environ_cb(RETRO_ENVIRONMENT_GET_LOG_INTERFACE, &log))
      log_cb = log.log;
   else
      log_cb = fallback_log;

   CDUtility_Init();

   const char *dir = NULL;

   if (environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &dir) && dir)
   {
      snprintf(retro_base_directory, sizeof(retro_base_directory), "%s", dir);
   }
   else
   {
      /* TODO: Add proper fallback */
      log_cb(RETRO_LOG_WARN, "System directory is not defined. Fallback on using same dir as ROM for system directory later ...\n");
      failed_init = true;
   }

   if (environ_cb(RETRO_ENVIRONMENT_GET_SAVE_DIRECTORY, &dir) && dir)
   {
      // If save directory is defined use it, otherwise use system directory
      if (dir)
         snprintf(retro_save_directory, sizeof(retro_save_directory), "%s", dir);
      else
         snprintf(retro_save_directory, sizeof(retro_save_directory), "%s", retro_base_directory);
   }
   else
   {
      /* TODO: Add proper fallback */
      log_cb(RETRO_LOG_WARN, "Save directory is not defined. Fallback on using SYSTEM directory ...\n");
      snprintf(retro_save_directory, sizeof(retro_save_directory), "%s", retro_base_directory);
   }

   disc_init( environ_cb );

   if (environ_cb(RETRO_ENVIRONMENT_GET_PERF_INTERFACE, &perf_cb))
      perf_get_cpu_features_cb = perf_cb.get_cpu_features;
   else
      perf_get_cpu_features_cb = NULL;

   setting_region = 0; // auto
   setting_smpc_autortc = true;
   setting_smpc_autortc_lang = 0;
   setting_initial_scanline = 0;
   setting_last_scanline = 239;
   setting_initial_scanline_pal = 0;
   setting_last_scanline_pal = 287;

   check_system_specs();
}

void retro_reset(void)
{
   SS_Reset( true );
}

bool retro_load_game_special(unsigned, const struct retro_game_info *, size_t)
{
   return false;
}

static bool old_cdimagecache = false;

static bool boot = true;

// shared memory cards support
static bool shared_memorycards = false;
static bool shared_memorycards_toggle = false;

static void check_variables(bool startup)
{
   struct retro_variable var = {0};

   if (startup)
   {
   }

   var.key = "beetle_saturn_region";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      if (!strcmp(var.value, "Auto Detect") || !strcmp(var.value, "auto"))
         setting_region = 0;
      else if (!strcmp(var.value, "Japan") || !strcmp(var.value, "jp"))
         setting_region = SMPC_AREA_JP;
      else if (!strcmp(var.value, "North America") || !strcmp(var.value, "na"))
         setting_region = SMPC_AREA_NA;
      else if (!strcmp(var.value, "Europe") || !strcmp(var.value, "eu"))
         setting_region = SMPC_AREA_EU_PAL;
      else if (!strcmp(var.value, "South Korea") || !strcmp(var.value, "kr"))
         setting_region = SMPC_AREA_KR;
      else if (!strcmp(var.value, "Asia (NTSC)") || !strcmp(var.value, "tw"))
         setting_region = SMPC_AREA_ASIA_NTSC;
      else if (!strcmp(var.value, "Asia (PAL)") || !strcmp(var.value, "as"))
         setting_region = SMPC_AREA_ASIA_PAL;
      else if (!strcmp(var.value, "Brazil") || !strcmp(var.value, "br"))
         setting_region = SMPC_AREA_CSA_NTSC;
      else if (!strcmp(var.value, "Latin America") || !strcmp(var.value, "la"))
         setting_region = SMPC_AREA_CSA_PAL;
   }

   var.key = "beetle_saturn_cart";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      if (!strcmp(var.value, "Auto Detect") || !strcmp(var.value, "auto"))
         setting_cart = CART__RESERVED;
      else if (!strcmp(var.value, "None") || !strcmp(var.value, "none"))
         setting_cart = CART_NONE;
      else if (!strcmp(var.value, "Backup Memory") || !strcmp(var.value, "backup"))
         setting_cart = CART_BACKUP_MEM;
      else if (!strcmp(var.value, "Extended RAM (1MB)") || !strcmp(var.value, "extram1"))
         setting_cart = CART_EXTRAM_1M;
      else if (!strcmp(var.value, "Extended RAM (4MB)") || !strcmp(var.value, "extram4"))
         setting_cart = CART_EXTRAM_4M;
      else if (!strcmp(var.value, "The King of Fighters '95") || !strcmp(var.value, "kof95"))
         setting_cart = CART_KOF95;
      else if (!strcmp(var.value, "Ultraman: Hikari no Kyojin Densetsu") || !strcmp(var.value, "ultraman"))
         setting_cart = CART_ULTRAMAN;
   }

   var.key = "beetle_saturn_multitap_port1";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      bool connected = false;
      if (!strcmp(var.value, "enabled"))
         connected = true;
      else if (!strcmp(var.value, "disabled"))
         connected = false;

      input_multitap( 1, connected );
   }

   var.key = "beetle_saturn_multitap_port2";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      bool connected = false;
      if (!strcmp(var.value, "enabled"))
         connected = true;
      else if (!strcmp(var.value, "disabled"))
         connected = false;

      input_multitap( 2, connected );
   }

   var.key = "beetle_saturn_cdimagecache";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      bool cdimage_cache = true;
      if (!strcmp(var.value, "enabled"))
         cdimage_cache = true;
      else if (!strcmp(var.value, "disabled"))
         cdimage_cache = false;
      if (cdimage_cache != old_cdimagecache)
      {
         old_cdimagecache = cdimage_cache;
      }
   }

   var.key = "beetle_saturn_autortc";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      if (!strcmp(var.value, "enabled"))
         setting_smpc_autortc = 1;
      else if (!strcmp(var.value, "disabled"))
         setting_smpc_autortc = 0;
   }

   var.key = "beetle_saturn_autortc_lang";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
       if (!strcmp(var.value, "english"))
          setting_smpc_autortc_lang = 0;
       else if (!strcmp(var.value, "german"))
          setting_smpc_autortc_lang = 1;
       else if (!strcmp(var.value, "french"))
          setting_smpc_autortc_lang = 2;
       else if (!strcmp(var.value, "spanish"))
          setting_smpc_autortc_lang = 3;
       else if (!strcmp(var.value, "italian"))
          setting_smpc_autortc_lang = 4;
       else if (!strcmp(var.value, "japanese"))
          setting_smpc_autortc_lang = 5;
   }

   var.key = "beetle_saturn_horizontal_overscan";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      h_mask = atoi(var.value);
   }

   var.key = "beetle_saturn_initial_scanline";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      first_sl = atoi(var.value);
   }

   var.key = "beetle_saturn_last_scanline";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      last_sl = atoi(var.value);
   }

   var.key = "beetle_saturn_initial_scanline_pal";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      first_sl_pal = atoi(var.value);
   }

   var.key = "beetle_saturn_last_scanline_pal";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      last_sl_pal = atoi(var.value);
   }

   var.key = "beetle_saturn_horizontal_blend";

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value)
   {
      bool newval = (!strcmp(var.value, "enabled"));
      DoHBlend = newval;
   }

   var.key = "beetle_saturn_analog_stick_deadzone";
   var.value = NULL;

   if ( environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value )
      input_set_deadzone_stick( atoi( var.value ) );

   var.key = "beetle_saturn_trigger_deadzone";
   var.value = NULL;

   if ( environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value )
      input_set_deadzone_trigger( atoi( var.value ) );

   var.key = "beetle_saturn_mouse_sensitivity";
   var.value = NULL;

   if ( environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value )
      input_set_mouse_sensitivity( atoi( var.value ) );

   var.key = "beetle_saturn_virtuagun_crosshair";
   var.value = NULL;

   if ( environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE, &var) && var.value )
   {
      if ( !strcmp(var.value, "Off") ) {
         setting_gun_crosshair = SETTING_GUN_CROSSHAIR_OFF;
      } else if ( !strcmp(var.value, "Cross") ) {
         setting_gun_crosshair = SETTING_GUN_CROSSHAIR_CROSS;
      } else if ( !strcmp(var.value, "Dot") ) {
         setting_gun_crosshair = SETTING_GUN_CROSSHAIR_DOT;
      }
   }
}

static bool MDFNI_LoadGame( const char *name )
{
   unsigned horrible_hacks   = 0;
   // .. safe defaults
   unsigned region           = SMPC_AREA_NA;
   int cart_type             = CART_BACKUP_MEM;
   unsigned cpucache_emumode = CPUCACHE_EMUMODE_DATA;

   // always set this.
   MDFNGameInfo = &EmulatedSS;

   size_t name_len = strlen( name );

   // check for a valid file extension
   if ( name_len > 4 )
   {
      const char *ext = name + name_len - 4;

      // supported extension?
      if ((!strcasecmp( ext, ".ccd" )) ||
          (!strcasecmp( ext, ".chd" )) ||
          (!strcasecmp( ext, ".cue" )) ||
          (!strcasecmp( ext, ".toc" )) ||
          (!strcasecmp( ext, ".m3u" )) )
      {
         uint8 fd_id[16];
         char sgid[16 + 1] = { 0 };

         if ( disc_load_content( MDFNGameInfo, name, fd_id, sgid ) )
         {
            log_cb(RETRO_LOG_INFO, "Game ID is: %s\n", sgid );

            // test discs?
            bool discs_ok = true;
            if ( setting_disc_test )
               discs_ok = DiscSanityChecks();

            if ( discs_ok )
            {
               DetectRegion( &region );

               DB_Lookup(nullptr, sgid, fd_id, &region, &cart_type, &cpucache_emumode );
               horrible_hacks = DB_LookupHH(sgid, fd_id);

               // forced region setting?
               if ( setting_region != 0 )
                  region = setting_region;

               // forced cartridge setting?
               if ( setting_cart != CART__RESERVED )
                  cart_type = setting_cart;

               // GO!
               if ( InitCommon( cpucache_emumode,
                    horrible_hacks, cart_type, region ) )
               {
                  MDFN_LoadGameCheats(NULL);
                  MDFNMP_InstallReadPatches();

                  return true;
               }

               // OK it's really bad. Probably don't 
               // have a BIOS if InitCommon
               // fails. We can't continue as an 
               // emulator and will show a blank
               // screen.

               disc_cleanup();

               return false;
            } // discs okay?

         } // load content

      } // supported extension?

   } // valid name?

   //
   // Drop to BIOS

   disc_cleanup();

   // forced region setting?
   if ( setting_region != 0 )
      region = setting_region;

   // forced cartridge setting?
   if ( setting_cart != CART__RESERVED )
      cart_type = setting_cart;

   // Initialise with safe parameters
   InitCommon( cpucache_emumode, horrible_hacks, cart_type, region );

   MDFN_LoadGameCheats(NULL);
   MDFNMP_InstallReadPatches();

   return true;
}

bool retro_load_game(const struct retro_game_info *info)
{
   char tocbasepath[4096];
   bool ret = false;

   if (!info || failed_init)
      return false;

   input_init_env( environ_cb );

   enum retro_pixel_format fmt = RETRO_PIXEL_FORMAT_XRGB8888;
   if (!environ_cb(RETRO_ENVIRONMENT_SET_PIXEL_FORMAT, &fmt))
      return false;

   extract_basename(retro_cd_base_name,       info->path, sizeof(retro_cd_base_name));
   extract_directory(retro_cd_base_directory, info->path, sizeof(retro_cd_base_directory));

   snprintf(tocbasepath, sizeof(tocbasepath), "%s" RETRO_SLASH "%s.toc", retro_cd_base_directory, retro_cd_base_name);

   if (filestream_exists(tocbasepath))
      snprintf(retro_cd_path, sizeof(retro_cd_path), "%s", tocbasepath);
   else
      snprintf(retro_cd_path, sizeof(retro_cd_path), "%s", info->path);

   check_variables(true);
   //make sure shared memory cards and save states are enabled only at startup
   shared_memorycards = shared_memorycards_toggle;

   // Let's try to load the game. If this fails then things are very wrong.
   if (MDFNI_LoadGame(retro_cd_path) == false)
      return false;

   MDFN_LoadGameCheats(NULL);
   MDFNMP_InstallReadPatches();

   alloc_surface();

#ifdef NEED_DEINTERLACER
   PrevInterlaced = false;
   deint.ClearState();
#endif

   input_init();

   boot = false;

   disc_select(0);

   frame_count = 0;
   internal_frame_count = 0;

   return true;
}

void retro_unload_game(void)
{
   if(!MDFNGameInfo)
      return;

   MDFN_FlushGameCheats(0);

   CloseGame();

   if (MDFNGameInfo->RMD)
   {
      delete MDFNGameInfo->RMD;
      MDFNGameInfo->RMD = NULL;
   }

   MDFNMP_Kill();

   MDFNGameInfo = NULL;

   disc_cleanup();

   retro_cd_base_directory[0] = '\0';
   retro_cd_path[0]           = '\0';
   retro_cd_base_name[0]      = '\0';
}

static uint64_t video_frames, audio_frames;
#define SOUND_CHANNELS 2

void retro_run(void)
{
   bool updated = false;
   bool hires_h_mode;
   unsigned overscan_mask;
   unsigned linevisfirst, linevislast;
   static unsigned width, height;
   static unsigned game_width, game_height;

   if (environ_cb(RETRO_ENVIRONMENT_GET_VARIABLE_UPDATE, &updated) && updated)
      check_variables(false);

   linevisfirst   =  is_pal ? first_sl_pal : first_sl;
   linevislast    =  is_pal ? last_sl_pal : last_sl;

   // Keep the counters at 0 so that they don't display a bogus
   // value if this option is enabled later on
   frame_count = 0;
   internal_frame_count = 0;

   input_poll_cb();

   input_update( input_state_cb );

   static int32 rects[MEDNAFEN_CORE_GEOMETRY_MAX_H];
   rects[0] = ~0;

   static int16_t sound_buf[0x10000];
   EmulateSpecStruct spec;
   spec.surface = surf;
   spec.SoundRate = 44100;
   spec.SoundBuf = sound_buf;
   spec.LineWidths = rects;
   spec.SoundBufMaxSize = sizeof(sound_buf) / 2;
   spec.SoundVolume = 1.0;
   spec.soundmultiplier = 1.0;
   spec.SoundBufSize = 0;
   spec.VideoFormatChanged = false;
   spec.SoundFormatChanged = false;

   EmulateSpecStruct *espec = (EmulateSpecStruct*)&spec;

   if (spec.SoundRate != last_sound_rate)
   {
      spec.SoundFormatChanged = true;
      last_sound_rate = spec.SoundRate;
   }

   Emulate(espec);

#ifdef NEED_DEINTERLACER
   if (spec.InterlaceOn)
   {
      if (!PrevInterlaced)
         deint.ClearState();

      deint.Process(spec.surface, spec.DisplayRect, spec.LineWidths, spec.InterlaceField);

      PrevInterlaced = true;

      spec.InterlaceOn = false;
      spec.InterlaceField = 0;
   }
   else
      PrevInterlaced = false;

#endif
   const void *fb      = NULL;
   const uint32_t *pix = surf->pixels;
   size_t pitch        = FB_WIDTH * sizeof(uint32_t);

   hires_h_mode   =  (rects[0] == 704) ? true : false;
   overscan_mask  =  (h_mask >> 1) << hires_h_mode;
   width          =  rects[0] - (h_mask << hires_h_mode);
   height         =  (linevislast + 1 - linevisfirst) << PrevInterlaced;

   if (width != game_width || height != game_height)
   {
      struct retro_system_av_info av_info;

      // Change frontend resolution using  base width/height (+ overscan adjustments).
      // This avoids inconsistent frame scales when game switches between interlaced and non-interlaced modes.
      av_info.geometry.base_width   = 352 - h_mask;
      av_info.geometry.base_height  = linevislast + 1 - linevisfirst;
      av_info.geometry.max_width    = MEDNAFEN_CORE_GEOMETRY_MAX_W;
      av_info.geometry.max_height   = MEDNAFEN_CORE_GEOMETRY_MAX_H;
      av_info.geometry.aspect_ratio = MEDNAFEN_CORE_GEOMETRY_ASPECT_RATIO;
      environ_cb(RETRO_ENVIRONMENT_SET_GEOMETRY, &av_info);

      log_cb(RETRO_LOG_INFO, "Target framebuffer size : %dx%d\n", width, height);

      game_width  = width;
      game_height = height;

      input_set_geometry( width, height );
   }

   pix += surf->pitchinpix * (linevisfirst << PrevInterlaced) + overscan_mask;

   fb = pix;

   video_cb(fb, game_width, game_height, pitch);

   video_frames++;
   audio_frames += spec.SoundBufSize;

   int16_t *interbuf = (int16_t*)&IBuffer;

   audio_batch_cb(interbuf, spec.SoundBufSize);
}

void retro_get_system_info(struct retro_system_info *info)
{
#ifndef GIT_VERSION
#define GIT_VERSION ""
#endif
   memset(info, 0, sizeof(*info));
   info->library_name     = MEDNAFEN_CORE_NAME;
   info->library_version  = MEDNAFEN_CORE_VERSION GIT_VERSION;
   info->need_fullpath    = true;
   info->valid_extensions = MEDNAFEN_CORE_EXTENSIONS;
   info->block_extract    = false;
}

void retro_get_system_av_info(struct retro_system_av_info *info)
{
   memset(info, 0, sizeof(*info));
   info->timing.sample_rate    = 44100;
   info->geometry.base_width   = MEDNAFEN_CORE_GEOMETRY_BASE_W;
   info->geometry.base_height  = MEDNAFEN_CORE_GEOMETRY_BASE_H;
   info->geometry.max_width    = MEDNAFEN_CORE_GEOMETRY_MAX_W;
   info->geometry.max_height   = MEDNAFEN_CORE_GEOMETRY_MAX_H;
   info->geometry.aspect_ratio = MEDNAFEN_CORE_GEOMETRY_ASPECT_RATIO;

   if (retro_get_region() == RETRO_REGION_PAL)
      info->timing.fps            = 49.96;
   else
      info->timing.fps            = 59.88;
}

void retro_deinit(void)
{
   delete surf;
   surf = NULL;

   log_cb(RETRO_LOG_INFO, "[%s]: Samples / Frame: %.5f\n",
         MEDNAFEN_CORE_NAME, (double)audio_frames / video_frames);
   log_cb(RETRO_LOG_INFO, "[%s]: Estimated FPS: %.5f\n",
         MEDNAFEN_CORE_NAME, (double)video_frames * 44100 / audio_frames);
}

unsigned retro_get_region(void)
{
   if (is_pal)
       return RETRO_REGION_PAL;  //Ben Swith PAL
   else
       return RETRO_REGION_NTSC;
}

unsigned retro_api_version(void)
{
   return RETRO_API_VERSION;
}

void retro_set_environment( retro_environment_t cb )
{
   struct retro_vfs_interface_info vfs_iface_info;
   environ_cb = cb;

   static const struct retro_variable vars[] = {
      { "beetle_saturn_region", "System Region; Auto Detect|Japan|North America|Europe|South Korea|Asia (NTSC)|Asia (PAL)|Brazil|Latin America" },
      { "beetle_saturn_cart", "Cartridge; Auto Detect|None|Backup Memory|Extended RAM (1MB)|Extended RAM (4MB)|The King of Fighters '95|Ultraman: Hikari no Kyojin Densetsu" },
      { "beetle_saturn_multitap_port1", "6Player Adaptor on Port 1; disabled|enabled" },
      { "beetle_saturn_multitap_port2", "6Player Adaptor on Port 2; disabled|enabled" },
      { "beetle_saturn_analog_stick_deadzone", "Analog Stick Deadzone; 15%|20%|25%|30%|0%|5%|10%"},
      { "beetle_saturn_trigger_deadzone", "Trigger Deadzone; 15%|20%|25%|30%|0%|5%|10%"},
      { "beetle_saturn_mouse_sensitivity", "Mouse Sensitivity; 100%|105%|110%|115%|120%|125%|130%|135%|140%|145%|150%|155%|160%|165%|170%|175%|180%|185%|190%|195%|200%|5%|10%|15%|20%|25%|30%|35%|40%|45%|50%|55%|60%|65%|70%|75%|80%|85%|90%|95%" },
      { "beetle_saturn_virtuagun_crosshair", "Gun Crosshair; Cross|Dot|Off" },
      { "beetle_saturn_cdimagecache", "CD Image Cache (restart); disabled|enabled" },
      { "beetle_saturn_autortc", "Automatically set RTC on game load; enabled|disabled" },
      { "beetle_saturn_autortc_lang", "BIOS language; english|german|french|spanish|italian|japanese" },
      { "beetle_saturn_horizontal_overscan", "Horizontal Overscan Mask; 0|2|4|6|8|10|12|14|16|18|20|22|24|26|28|30|32|34|36|38|40|42|44|46|48|50|52|54|56|58|60" },
      { "beetle_saturn_initial_scanline", "Initial scanline; 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31|32|33|34|35|36|37|38|39|40" },
      { "beetle_saturn_last_scanline", "Last scanline; 239|210|211|212|213|214|215|216|217|218|219|220|221|222|223|224|225|226|227|228|229|230|231|232|233|234|235|236|237|238" },
      { "beetle_saturn_initial_scanline_pal", "Initial scanline PAL; 16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31|32|33|34|35|36|37|38|39|40|41|42|43|44|45|46|47|48|49|50|51|52|53|54|55|56|57|58|59|60|0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15" },
      { "beetle_saturn_last_scanline_pal", "Last scanline PAL; 271|272|273|274|275|276|277|278|279|280|281|282|283|284|285|286|287|230|231|232|233|234|235|236|237|238|239|240|241|242|243|244|245|246|247|248|249|250|251|252|253|254|255|256|257|258|259|260|261|262|263|264|265|266|267|268|269|270" },
      { "beetle_saturn_horizontal_blend", "Enable Horizontal Blend(blur); disabled|enabled" },
      { NULL, NULL },
   };

   cb(RETRO_ENVIRONMENT_SET_VARIABLES, (void*)vars);

   vfs_iface_info.required_interface_version = 1;
   vfs_iface_info.iface                      = NULL;
   if (environ_cb(RETRO_ENVIRONMENT_GET_VFS_INTERFACE, &vfs_iface_info))
      filestream_vfs_init(&vfs_iface_info);

   input_set_env( cb );
}

void retro_set_audio_sample(retro_audio_sample_t cb)
{
   audio_cb = cb;
}

void retro_set_audio_sample_batch(retro_audio_sample_batch_t cb)
{
   audio_batch_cb = cb;
}

void retro_set_input_poll(retro_input_poll_t cb)
{
   input_poll_cb = cb;
}

void retro_set_input_state(retro_input_state_t cb)
{
   input_state_cb = cb;
}

void retro_set_video_refresh(retro_video_refresh_t cb)
{
   video_cb = cb;
}

static size_t serialize_size = 0;

size_t retro_serialize_size(void)
{
   // Don't know yet?
   if ( serialize_size == 0 )
   {
      // Do a fake save to see.
      StateMem st;

      st.data           = NULL;
      st.loc            = 0;
      st.len            = 0;
      st.malloced       = 0;
      st.initial_malloc = 0;

      if ( MDFNSS_SaveSM( &st, MEDNAFEN_CORE_VERSION_NUMERIC, NULL, NULL, NULL ) )
      {
         // Cache and tidy up.
         serialize_size = st.len;
         if (st.data)
            free(st.data);
      }
   }

   // Return cached value.
   return serialize_size;
}

bool retro_serialize(void *data, size_t size)
{
   /* it seems that mednafen can realloc pointers sent to it?
      since we don't know the disposition of void* data (is it safe to realloc?) we have to manage a new buffer here */
   StateMem st;
   bool ret          = false;
   uint8_t *_dat     = (uint8_t*)malloc(size);

   st.data           = _dat;
   st.loc            = 0;
   st.len            = 0;
   st.malloced       = size;
   st.initial_malloc = 0;

   ret               = MDFNSS_SaveSM(&st, MEDNAFEN_CORE_VERSION_NUMERIC, NULL, NULL, NULL);

   /* there are still some errors with the save states, the size seems to change on some games for now just log when this happens */
   if (st.len != size)
      log_cb(RETRO_LOG_WARN, "warning, save state size has changed\n");

   memcpy(data,st.data,size);
   free(st.data);
   return ret;
}

bool retro_unserialize(const void *data, size_t size)
{
   StateMem st;

   st.data           = (uint8_t*)data;
   st.loc            = 0;
   st.len            = size;
   st.malloced       = 0;
   st.initial_malloc = 0;

   return MDFNSS_LoadSM(&st, MEDNAFEN_CORE_VERSION_NUMERIC);
}

void *retro_get_memory_data(unsigned type)
{
   switch ( type & RETRO_MEMORY_MASK )
   {

   case RETRO_MEMORY_SYSTEM_RAM:
      return WorkRAM;

   }

   // not supported
   return NULL;
}

size_t retro_get_memory_size(unsigned type)
{
   switch ( type & RETRO_MEMORY_MASK )
   {

   case RETRO_MEMORY_SYSTEM_RAM:
      return sizeof(WorkRAM);

   }

   // not supported
   return 0;
}

void retro_cheat_reset(void)
{}

void retro_cheat_set(unsigned, bool, const char *)
{}

#ifdef _WIN32
static void sanitize_path(std::string &path)
{
   size_t size = path.size();
   for (size_t i = 0; i < size; i++)
      if (path[i] == '/')
         path[i] = '\\';
}
#endif

// Use a simpler approach to make sure that things go right for libretro.
const char *MDFN_MakeFName(MakeFName_Type type, int id1, const char *cd1)
{
   static char fullpath[4096];

   fullpath[0] = '\0';

   switch (type)
   {
      case MDFNMKF_SAV:
         snprintf(fullpath, sizeof(fullpath), "%s" RETRO_SLASH "%s.%s",
               retro_save_directory,
               (!shared_memorycards) ? retro_cd_base_name : "mednafen_saturn_libretro_shared",
               cd1);
         break;
      case MDFNMKF_FIRMWARE:
         snprintf(fullpath, sizeof(fullpath), "%s" RETRO_SLASH "%s", retro_base_directory, cd1);
         break;
      default:
         break;
   }

   return fullpath;
}

void MDFND_DispMessage(unsigned char *str)
{
   const char *strc = (const char*)str;
   struct retro_message msg =
   {
      strc,
      180
   };

   environ_cb(RETRO_ENVIRONMENT_SET_MESSAGE, &msg);
}

void MDFN_DispMessage(const char *format, ...)
{
   char *str = new char[4096];
   struct retro_message msg;
   va_list ap;
   va_start(ap,format);
   const char *strc = NULL;

   vsnprintf(str, 4096, format, ap);
   va_end(ap);
   strc = str;

   msg.frames = 180;
   msg.msg = strc;

   environ_cb(RETRO_ENVIRONMENT_SET_MESSAGE, &msg);
}

void MDFN_MidSync(void)
{
    input_poll_cb();
    input_update( input_state_cb );
}
