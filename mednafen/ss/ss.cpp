/******************************************************************************/
/* Mednafen Sega Saturn Emulation Module                                      */
/******************************************************************************/
/* ss.cpp - Saturn Core Emulation and Support Functions
**  Copyright (C) 2015-2020 Mednafen Team
**
** This program is free software; you can redistribute it and/or
** modify it under the terms of the GNU General Public License
** as published by the Free Software Foundation; either version 2
** of the License, or (at your option) any later version.
**
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
**
** You should have received a copy of the GNU General Public License
** along with this program; if not, write to the Free Software Foundation, Inc.,
** 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
*/

// WARNING: Be careful with 32-bit access to 16-bit space, bus locking, etc. in respect to DMA and event updates(and where they can occur).

#include "../mednafen.h"
#include "../mempatcher.h"
#include "../git.h"
#include "../general.h"
#include "../cdrom/cdromif.h"
#include "../FileStream.h"
#include "../hash/sha256.h"
#include "../hash/md5.h"
#include "ss.h"
#include "debug.inc"

#include "../../disc.h"

#include <bitset>
#include <retro_miscellaneous.h>

#include <zlib.h>

extern MDFNGI EmulatedSS;

#include "ss.h"
#include "sound.h"
#include "scsp.h" // For debug.inc
#include "smpc.h"
#include "cdb.h"
#include "vdp1.h"
#include "vdp2.h"
#include "scu.h"
#include "cart.h"
#include "db.h"


// Libretro-specific
#ifndef RETRO_SLASH
#ifdef _WIN32
#define RETRO_SLASH "\\"
#else
#define RETRO_SLASH "/"
#endif
#endif
#include "../../libretro_settings.h"
#include "../../input.h"
extern void MDFN_MidSync(void);
extern bool is_pal;
extern char retro_base_directory[4096];

static sscpu_timestamp_t MidSync(const sscpu_timestamp_t timestamp);

#ifdef MDFN_ENABLE_DEV_BUILD
uint32 ss_dbg_mask;
static std::bitset<0x200> BWMIgnoreAddr[2]; // 0=read, 1=write

void SS_DBG(uint32 which, const char* format, ...)
{
 if(MDFN_LIKELY(!(ss_dbg_mask & which)))
  return;
 //
 va_list ap;
 va_start(ap, format);
 trio_vprintf(format, ap);
 va_end(ap);
}

void SS_DBGTI(uint32 which, const char* format, ...)
{
 if(MDFN_LIKELY(!(ss_dbg_mask & which)))
  return;
 //
 va_list ap;
 va_start(ap, format);
 trio_vprintf(format, ap);
 va_end(ap);
 //
 trio_printf(" @Line=0x%03x, HPos=0x%03x, memts=%d\n", VDP2::PeekLine(), VDP2::PeekHPos(), SH7095_mem_timestamp);
}
#endif
uint32 ss_horrible_hacks;

static bool NeedEmuICache;
static const uint8 BRAM_Init_Data[0x10] = { 0x42, 0x61, 0x63, 0x6b, 0x55, 0x70, 0x52, 0x61, 0x6d, 0x20, 0x46, 0x6f, 0x72, 0x6d, 0x61, 0x74 };

static void SaveBackupRAM(void);
static void LoadBackupRAM(void);
static void SaveCartNV(void);
static void LoadCartNV(void);
static void SaveRTC(void);
static void LoadRTC(void);

static MDFN_COLD void BackupBackupRAM(void);
static MDFN_COLD void BackupCartNV(void);

#include "sh7095.h"

static uint8 SCU_MSH2VectorFetch(void);
static uint8 SCU_SSH2VectorFetch(void);

static void CheckEventsByMemTS(void);

SH7095 CPU[2]{ {"SH2-M", SS_EVENT_SH2_M_DMA, SCU_MSH2VectorFetch}, {"SH2-S", SS_EVENT_SH2_S_DMA, SCU_SSH2VectorFetch}};

static uint16 BIOSROM[524288 / sizeof(uint16)];
uint8 WorkRAM[2*WORKRAM_BANK_SIZE_BYTES]; // unified 2MB work ram for linear access.
// Effectively 32-bit in reality, but 16-bit here because of CPU interpreter design(regarding fastmap).
static uint16* WorkRAML = (uint16*)(WorkRAM + (WORKRAM_BANK_SIZE_BYTES*0));
static uint16* WorkRAMH = (uint16*)(WorkRAM + (WORKRAM_BANK_SIZE_BYTES*1));
static uint8 BackupRAM[32768];
static bool BackupRAM_Dirty;
static int64 BackupRAM_SaveDelay;
static int64 CartNV_SaveDelay;

#define SH7095_EXT_MAP_GRAN_BITS 16
static uintptr_t SH7095_FastMap[1U << (32 - SH7095_EXT_MAP_GRAN_BITS)];

int32 SH7095_mem_timestamp;
static uint32 SH7095_BusLock;
static uint32 SH7095_DB;

#include "scu.inc"

static sha256_digest BIOS_SHA256;   // SHA-256 hash of the currently-loaded BIOS; used for save state sanity checks.
static int ActiveCartType;		// Used in save states.
static std::bitset<1U << (27 - SH7095_EXT_MAP_GRAN_BITS)> FMIsWriteable;
static uint16 fmap_dummy[(1U << SH7095_EXT_MAP_GRAN_BITS) / sizeof(uint16)];

/*
 SH-2 external bus address map:
  CS0: 0x00000000...0x01FFFFFF (16-bit)
   0x00000000...0x000FFFFF: BIOS ROM (R)
   0x00100000...0x0017FFFF: SMPC (R/W; 8-bit mapped as 16-bit)
   0x00180000...0x001FFFFF: Backup RAM(32KiB) (R/W; 8-bit mapped as 16-bit)
   0x00200000...0x003FFFFF: Low RAM(1MiB) (R/W)
   0x01000000...0x017FFFFF: Slave FRT Input Capture Trigger (W)
   0x01800000...0x01FFFFFF: Master FRT Input Capture Trigger (W)

  CS1: 0x02000000...0x03FFFFFF (SCU managed)
   0x02000000...0x03FFFFFF: A-bus CS0 (R/W)

  CS2: 0x04000000...0x05FFFFFF (SCU managed)
   0x04000000...0x04FFFFFF: A-bus CS1 (R/W)
   0x05000000...0x057FFFFF: A-bus Dummy
   0x05800000...0x058FFFFF: A-bus CS2 (R/W)
   0x05A00000...0x05AFFFFF: SCSP RAM (R/W)
   0x05B00000...0x05BFFFFF: SCSP Registers (R/W)
   0x05C00000...0x05C7FFFF: VDP1 VRAM (R/W)
   0x05C80000...0x05CFFFFF: VDP1 FB RAM (R/W; swappable between two framebuffers, but may be temporarily unreadable at swap time)
   0x05D00000...0x05D7FFFF: VDP1 Registers (R/W)
   0x05E00000...0x05EFFFFF: VDP2 VRAM (R/W)
   0x05F00000...0x05F7FFFF: VDP2 CRAM (R/W; 8-bit writes are illegal)
   0x05F80000...0x05FBFFFF: VDP2 Registers (R/W; 8-bit writes are illegal)
   0x05FE0000...0x05FEFFFF: SCU Registers (R/W)
   0x05FF0000...0x05FFFFFF: SCU Debug/Test Registers (R/W)

  CS3: 0x06000000...0x07FFFFFF
   0x06000000...0x07FFFFFF: High RAM/SDRAM(1MiB) (R/W)
*/
//
// Never add anything to SH7095_mem_timestamp when DMAHax is true.
//
// When BurstHax is true and we're accessing high work RAM, don't add anything.
//
template<typename T, bool IsWrite>
static INLINE void BusRW_DB_CS0(const uint32 A, uint32& DB, const bool BurstHax, int32* SH2DMAHax)
{
 //
 // Low(and kinda slow) work RAM
 //
 if(A >= 0x00200000 && A <= 0x003FFFFF)
 {
#if 0
  if(A & 0x100000)
  {
   if(IsWrite)
    SS_DBG(SS_DBG_WARNING, "[RAM] %zu-byte write of 0x%08x to mirrored address 0x%08x\n", sizeof(T), DB >> (((A & 1) ^ (2 - sizeof(T))) << 3), A);
   else
    SS_DBG(SS_DBG_WARNING, "[RAM] %zu-byte read from mirrored address 0x%08x\n", sizeof(T), A);
  }
#endif

  if(IsWrite)
   ne16_wbo_be<T>(WorkRAML, A & 0xFFFFF, DB >> (((A & 1) ^ (2 - sizeof(T))) << 3));
  else
   DB = (DB & 0xFFFF0000) | ne16_rbo_be<uint16>(WorkRAML, A & 0xFFFFE);

  if(!SH2DMAHax)
   SH7095_mem_timestamp += 7;
  else
   *SH2DMAHax += 7;

  return;
 }

 //
 // BIOS ROM
 //
 if(A >= 0x00000000 && A <= 0x000FFFFF)
 {
  if(!SH2DMAHax)
   SH7095_mem_timestamp += 8;
  else
   *SH2DMAHax += 8;

  if(!IsWrite)
   DB = (DB & 0xFFFF0000) | ne16_rbo_be<uint16>(BIOSROM, A & 0x7FFFE);

  return;
 }

 //
 // SMPC
 //
 if(A >= 0x00100000 && A <= 0x0017FFFF)
 {
  const uint32 SMPC_A = (A & 0x7F) >> 1;

  if(!SH2DMAHax)
  {
   // SH7095_mem_timestamp += 2;
   CheckEventsByMemTS();
  }

  if(IsWrite)
  {
   if(sizeof(T) == 2 || (A & 1))
    SMPC_Write(SH7095_mem_timestamp, SMPC_A, DB);
  }
  else
   DB = (DB & 0xFFFF0000) | 0xFF00 | SMPC_Read(SH7095_mem_timestamp, SMPC_A);

  return;
 }

 //
 // Backup RAM
 //
 if(A >= 0x00180000 && A <= 0x001FFFFF)
 {
  if(!SH2DMAHax)
   SH7095_mem_timestamp += 8;
  else
   *SH2DMAHax += 8;

  if(IsWrite)
  {
   if(sizeof(T) != 1 || (A & 1))
   {
    BackupRAM[(A >> 1) & 0x7FFF] = DB;
    BackupRAM_Dirty = true;
   }
  }
  else
   DB = (DB & 0xFFFF0000) | 0xFF00 | BackupRAM[(A >> 1) & 0x7FFF];

  return;
 }

 //
 // FRT trigger region
 //
 if(A >= 0x01000000 && A <= 0x01FFFFFF)
 {
  if(!SH2DMAHax)
   SH7095_mem_timestamp += 8;
  else
   *SH2DMAHax -= 8;

  //printf("FT FRT%08x %zu %08x %04x %d %d\n", A, sizeof(T), A, V, SMPC_IsSlaveOn(), SH7095_mem_timestamp);
  if(IsWrite)
  {
   if(sizeof(T) != 1)
   {
    const unsigned c = ((A >> 23) & 1) ^ 1;

    CPU[c].SetFTI(true);
    CPU[c].SetFTI(false);
   }
  }
  return;
 }

 //
 //
 //
 if(!SH2DMAHax)
  SH7095_mem_timestamp += 4;
 else
  *SH2DMAHax += 4;

#if 0
 if(IsWrite)
  SS_DBG(SS_DBG_WARNING, "[SH2 BUS] Unknown %zu-byte write of 0x%08x to 0x%08x\n", sizeof(T), DB >> (((A & 1) ^ (2 - sizeof(T))) << 3), A);
 else
  SS_DBG(SS_DBG_WARNING, "[SH2 BUS] Unknown %zu-byte read from 0x%08x\n", sizeof(T), A);
#endif
}

template<typename T, bool IsWrite>
static INLINE void BusRW_DB_CS12(const uint32 A, uint32& DB, const bool BurstHax, int32* SH2DMAHax)
{
 //
 // CS1 and CS2: SCU
 //
 if(!IsWrite)
  DB = 0;

 SCU_FromSH2_BusRW_DB<T, IsWrite>(A, &DB, SH2DMAHax);
}

template<typename T, bool IsWrite>
static INLINE void BusRW_DB_CS3(const uint32 A, uint32& DB, const bool BurstHax, int32* SH2DMAHax)
{
 //
 // CS3: High work RAM/SDRAM, 0x06000000 ... 0x07FFFFFF
 //
 if(A >= 0x06000000)
 {
  if(!IsWrite || sizeof(T) == 4)
   ne16_rwbo_be<uint32, IsWrite>(WorkRAMH, A & 0xFFFFC, &DB);
  else
   ne16_wbo_be<T>(WorkRAMH, A & 0xFFFFF, DB >> (((A & 3) ^ (4 - sizeof(T))) << 3));

  if(!BurstHax)
  {
   if(!SH2DMAHax)
   {
    if(IsWrite)
    {
     SH7095_mem_timestamp = (SH7095_mem_timestamp + 4) &~ 3;
    }
    else
    {
     SH7095_mem_timestamp += 7;
    }
   }
   else
    *SH2DMAHax -= IsWrite ? 3 : 6;
  }
 }
}

//
//
//
static MDFN_COLD uint8 CheatMemRead(uint32 A)
{
 A &= (1U << 27) - 1;

 return ne16_rbo_be<uint8>(SH7095_FastMap[A >> SH7095_EXT_MAP_GRAN_BITS], A);
}

static MDFN_COLD void CheatMemWrite(uint32 A, uint8 V)
{
 A &= (1U << 27) - 1;

 if(FMIsWriteable[A >> SH7095_EXT_MAP_GRAN_BITS])
 {
  ne16_wbo_be<uint8>(SH7095_FastMap[A >> SH7095_EXT_MAP_GRAN_BITS], A, V);

  for(unsigned c = 0; c < 2; c++)
  {
   if(CPU[c].CCR & SH7095::CCR_CE)
   {
    for(uint32 Abase = 0x00000000; Abase < 0x20000000; Abase += 0x08000000)
    {
     CPU[c].Cache_WriteUpdate<uint8>(Abase + A, V);
    }
   }
  }
 }
}
//
//
//
static void SetFastMemMap(uint32 Astart, uint32 Aend, uint16* ptr, uint32 length, bool is_writeable)
{
 const uint64 Abound = (uint64)Aend + 1;
 assert((Astart & ((1U << SH7095_EXT_MAP_GRAN_BITS) - 1)) == 0);
 assert((Abound & ((1U << SH7095_EXT_MAP_GRAN_BITS) - 1)) == 0);
 assert((length & ((1U << SH7095_EXT_MAP_GRAN_BITS) - 1)) == 0);
 assert(length > 0);
 assert(length <= (Abound - Astart));

 for(uint64 A = Astart; A < Abound; A += (1U << SH7095_EXT_MAP_GRAN_BITS))
 {
  uintptr_t tmp = (uintptr_t)ptr + ((A - Astart) % length);

  if(A < (1U << 27))
   FMIsWriteable[A >> SH7095_EXT_MAP_GRAN_BITS] = is_writeable;

  SH7095_FastMap[A >> SH7095_EXT_MAP_GRAN_BITS] = tmp - A;
 }
}

static MDFN_COLD void InitFastMemMap(void)
{
 for(unsigned i = 0; i < sizeof(fmap_dummy) / sizeof(fmap_dummy[0]); i++)
 {
  fmap_dummy[i] = 0;
 }

 FMIsWriteable.reset();
 MDFNMP_Init(1ULL << SH7095_EXT_MAP_GRAN_BITS, (1ULL << 27) / (1ULL << SH7095_EXT_MAP_GRAN_BITS));

 for(uint64 A = 0; A < 1ULL << 32; A += (1U << SH7095_EXT_MAP_GRAN_BITS))
 {
  SH7095_FastMap[A >> SH7095_EXT_MAP_GRAN_BITS] = (uintptr_t)fmap_dummy - A;
 }
}

void SS_SetPhysMemMap(uint32 Astart, uint32 Aend, uint16* ptr, uint32 length, bool is_writeable)
{
 assert(Astart < 0x20000000);
 assert(Aend < 0x20000000);

 if(!ptr)
 {
  ptr = fmap_dummy;
  length = sizeof(fmap_dummy);
 }

 for(uint32 Abase = 0; Abase < 0x40000000; Abase += 0x20000000)
  SetFastMemMap(Astart + Abase, Aend + Abase, ptr, length, is_writeable);
}

#include "sh7095.inc"

//
// Running is:
//   0 at end of (emulation) frame
//
//   1 during normal execution
//
//  -1 when we need to temporarily break out of the execution loop to
//     e.g. handle turning the slave CPU on or off, which we can't
//     safely do from an event handler due to the event handler
//     potentially being called from deep within the memory read/write
//     functions.
//
static int Running;
event_list_entry events[SS_EVENT__COUNT];

static sscpu_timestamp_t next_event_ts;

template<unsigned c>
static sscpu_timestamp_t SH_DMA_EventHandler(sscpu_timestamp_t et)
{
 if(et < SH7095_mem_timestamp)
 {
  //printf("SH-2 DMA %d reschedule %d->%d\n", c, et, SH7095_mem_timestamp);
  return SH7095_mem_timestamp;
 }

 // Must come after the (et < SH7095_mem_timestamp) check.
 if(MDFN_UNLIKELY(SH7095_BusLock))
  return et + 1;

 return CPU[c].DMA_Update(et);
}

//
//
//

static MDFN_COLD void InitEvents(void)
{
 for(unsigned i = 0; i < SS_EVENT__COUNT; i++)
 {
  if(i == SS_EVENT__SYNFIRST)
   events[i].event_time = 0;
  else if(i == SS_EVENT__SYNLAST)
   events[i].event_time = 0x7FFFFFFF;
  else
   events[i].event_time = 0; //SS_EVENT_DISABLED_TS;

  events[i].prev = (i > 0) ? &events[i - 1] : NULL;
  events[i].next = (i < (SS_EVENT__COUNT - 1)) ? &events[i + 1] : NULL;
 }

 events[SS_EVENT_SH2_M_DMA].event_handler = &SH_DMA_EventHandler<0>;
 events[SS_EVENT_SH2_S_DMA].event_handler = &SH_DMA_EventHandler<1>;

 events[SS_EVENT_SCU_DMA].event_handler = SCU_UpdateDMA;
 events[SS_EVENT_SCU_DSP].event_handler = SCU_UpdateDSP;

 events[SS_EVENT_SMPC].event_handler = SMPC_Update;

 events[SS_EVENT_VDP1].event_handler = VDP1::Update;
 events[SS_EVENT_VDP2].event_handler = VDP2::Update;

 events[SS_EVENT_CDB].event_handler = CDB_Update;

 events[SS_EVENT_SOUND].event_handler = SOUND_Update;

 events[SS_EVENT_CART].event_handler = CART_GetEventHandler();

 events[SS_EVENT_MIDSYNC].event_handler = MidSync;
 events[SS_EVENT_MIDSYNC].event_time = SS_EVENT_DISABLED_TS;
}

static void RebaseTS(const sscpu_timestamp_t timestamp)
{
 for(unsigned i = 0; i < SS_EVENT__COUNT; i++)
 {
  if(i == SS_EVENT__SYNFIRST || i == SS_EVENT__SYNLAST)
   continue;

  assert(events[i].event_time > timestamp);

  if(events[i].event_time != SS_EVENT_DISABLED_TS)
   events[i].event_time -= timestamp;
 }

 next_event_ts = events[SS_EVENT__SYNFIRST].next->event_time;
}

void SS_SetEventNT(event_list_entry* e, const sscpu_timestamp_t next_timestamp)
{
#ifdef MDFN_ENABLE_DEV_BUILD
 if(next_timestamp < SS_EVENT_DISABLED_TS && (next_timestamp < 0 || next_timestamp >= 0x40000000))
 {
  fprintf(stderr, "Event %u, bad next timestamp 0x%08x\n", (unsigned)(e - events), next_timestamp);
  abort();
 }
#endif

 if(next_timestamp < e->event_time)
 {
  event_list_entry *fe = e;

  do
  {
   fe = fe->prev;
  } while(next_timestamp < fe->event_time);

  // Remove this event from the list, temporarily of course.
  e->prev->next = e->next;
  e->next->prev = e->prev;

  // Insert into the list, just after "fe".
  e->prev = fe;
  e->next = fe->next;
  fe->next->prev = e;
  fe->next = e;

  e->event_time = next_timestamp;
 }
 else if(next_timestamp > e->event_time)
 {
  event_list_entry *fe = e;

  do
  {
   fe = fe->next;
  } while(next_timestamp > fe->event_time);

  // Remove this event from the list, temporarily of course
  e->prev->next = e->next;
  e->next->prev = e->prev;

  // Insert into the list, just BEFORE "fe".
  e->prev = fe->prev;
  e->next = fe;
  fe->prev->next = e;
  fe->prev = e;

  e->event_time = next_timestamp;
 }

 next_event_ts = ((Running > 0) ? events[SS_EVENT__SYNFIRST].next->event_time : 0);
}

// Called from debug.cpp too.
void ForceEventUpdates(const sscpu_timestamp_t timestamp)
{
 for(unsigned c = 0; c < 2; c++)
  CPU[c].ForceInternalEventUpdates();

 for(unsigned evnum = SS_EVENT__SYNFIRST + 1; evnum < SS_EVENT__SYNLAST; evnum++)
 {
  if(events[evnum].event_time != SS_EVENT_DISABLED_TS)
   SS_SetEventNT(&events[evnum], events[evnum].event_handler(timestamp));
 }

 next_event_ts = ((Running > 0) ? events[SS_EVENT__SYNFIRST].next->event_time : 0);
}

static INLINE bool EventHandler(const sscpu_timestamp_t timestamp)
{
 event_list_entry *e = NULL;

 while(timestamp >= (e = events[SS_EVENT__SYNFIRST].next)->event_time)  // If Running = 0, EventHandler() may be called even if there isn't an event per-se, so while() instead of do { ... } while
 {
#ifdef MDFN_ENABLE_DEV_BUILD
  const sscpu_timestamp_t etime = e->event_time;
#endif
  sscpu_timestamp_t nt;
  nt = e->event_handler(e->event_time);

#ifdef MDFN_ENABLE_DEV_BUILD
  if(MDFN_UNLIKELY(nt <= etime))
  {
   fprintf(stderr, "which=%d event_time=%d nt=%d timestamp=%d\n", (int)(e - events), etime, nt, timestamp);
   assert(nt > etime);
  }
#endif

  SS_SetEventNT(e, nt);
 }

 return Running > 0;
}

static void CheckEventsByMemTS_Sub(void)
{
 EventHandler(SH7095_mem_timestamp);
}

static void CheckEventsByMemTS(void)
{
 if(MDFN_UNLIKELY(SH7095_mem_timestamp >= next_event_ts))
  CheckEventsByMemTS_Sub();
}

void SS_RequestEHLExit(void)
{
 if(Running)
 {
  Running = -1;
  next_event_ts = 0;
 }
}

void SS_RequestMLExit(void)
{
 Running = 0;
 next_event_ts = 0;
}

#pragma GCC push_options
#pragma GCC optimize("O2,no-unroll-loops,no-peel-loops,no-crossjumping")
template<bool EmulateICache, bool DebugMode>
static INLINE int32 RunLoop_INLINE(EmulateSpecStruct* espec)
{
 sscpu_timestamp_t eff_ts = 0;

 for(unsigned c = 0; c < 2; c++)
  CPU[c].SetDebugMode(DebugMode);

 //printf("%d %d\n", SH7095_mem_timestamp, CPU[0].timestamp);
 do
 {
  SMPC_ProcessSlaveOffOn();
  //
  //
  Running = true;
  ForceEventUpdates(eff_ts);
  do
  {
   do
   {
    if(DebugMode)
    {
     DBG_SetEffTS(eff_ts);
     DBG_CPUHandler<0>();
    }

    CPU[0].Step<0, EmulateICache, DebugMode>();
    CPU[0].DMA_BusTimingKludge();

    if(EmulateICache)
    {
     if(DebugMode)
      CPU[1].RunSlaveUntil_Debug(CPU[0].timestamp);
     else
      CPU[1].RunSlaveUntil(CPU[0].timestamp);
    }
    else
    {
     while(MDFN_LIKELY(CPU[0].timestamp > CPU[1].timestamp))
     {
      if(DebugMode)
       DBG_CPUHandler<1>();

      CPU[1].Step<1, false, DebugMode>();
     }
    }

    eff_ts = CPU[0].timestamp;
    if(SH7095_mem_timestamp > eff_ts)
     eff_ts = SH7095_mem_timestamp;
    else
     SH7095_mem_timestamp = eff_ts;
   } while(MDFN_LIKELY(eff_ts < next_event_ts));
  } while(MDFN_LIKELY(EventHandler(eff_ts)));
 } while(MDFN_LIKELY(Running != 0));

 //printf(" End: %d %d -- %d\n", SH7095_mem_timestamp, CPU[0].timestamp, eff_ts);
 return eff_ts;
}

template<bool EmulateICache>
static NO_INLINE MDFN_HOT int32 RunLoop(EmulateSpecStruct* espec)
{
 return RunLoop_INLINE<EmulateICache, false>(espec);
}

template<bool EmulateICache>
static NO_INLINE MDFN_COLD int32 RunLoop_Debug(EmulateSpecStruct* espec)
{
 return RunLoop_INLINE<EmulateICache, true>(espec);
}

#pragma GCC pop_options

// Must not be called within an event or read/write handler.
void SS_Reset(bool powering_up)
{
 SH7095_BusLock = 0;

 if(powering_up)
 {
   memset(WorkRAM, 0x00, sizeof(WorkRAM));   // TODO: Check real hardware
 }

 if(powering_up)
 {
  CPU[0].TruePowerOn();
  CPU[1].TruePowerOn();
 }

 SCU_Reset(powering_up);
 CPU[0].Reset(powering_up);

 SMPC_Reset(powering_up);

 VDP1::Reset(powering_up);
 VDP2::Reset(powering_up);

 CDB_Reset(powering_up);

 SOUND_Reset(powering_up);

 CART_Reset(powering_up);
}

static EmulateSpecStruct* espec;
static bool AllowMidSync;
static int32 cur_clock_div;

static int64 UpdateInputLastBigTS;
static INLINE void UpdateSMPCInput(const sscpu_timestamp_t timestamp)
{
 SMPC_TransformInput();

 int32 elapsed_time = (((int64)timestamp * cur_clock_div * 1000 * 1000) - UpdateInputLastBigTS) / (EmulatedSS.MasterClock / MDFN_MASTERCLOCK_FIXED(1));

 UpdateInputLastBigTS += (int64)elapsed_time * (EmulatedSS.MasterClock / MDFN_MASTERCLOCK_FIXED(1));

 SMPC_UpdateInput(elapsed_time);
}

static sscpu_timestamp_t MidSync(const sscpu_timestamp_t timestamp)
{
 if(AllowMidSync)
 {
    //
    // Don't call SOUND_Update() here, it's not necessary and will subtly alter emulation behavior from the perspective of the emulated program
    // (which is not a problem in and of itself, but it's preferable to keep settings from altering emulation behavior when they don't need to).
    //
    //printf("MidSync: %d\n", VDP2::PeekLine());
    {
//       espec->SoundBufSize += SOUND_FlushOutput();
//       espec->MasterCycles = timestamp * cur_clock_div;
    }
    //printf("%d\n", espec->SoundBufSize);

    SMPC_UpdateOutput();

    MDFN_MidSync();

    UpdateSMPCInput(timestamp);

    AllowMidSync = false;
 }

 return SS_EVENT_DISABLED_TS;
}

void Emulate(EmulateSpecStruct* espec_arg)
{
 int32 end_ts;

 espec = espec_arg;
 AllowMidSync = true;

 cur_clock_div = SMPC_StartFrame(espec);
 UpdateSMPCInput(0);
 VDP2::StartFrame(espec, cur_clock_div == 61);
 CART_SetCPUClock(EmulatedSS.MasterClock / MDFN_MASTERCLOCK_FIXED(1), cur_clock_div);
 espec->SoundBufSize = 0;
 espec->MasterCycles = 0;
 espec->soundmultiplier = 1;
 //
 //
 //
#ifdef WANT_DEBUGGER
 #define RLTDAT(eic) RunLoop_Debug<eic>
#else
 #define RLTDAT(eic) RunLoop<eic>
#endif
 static int32 (*const rltab[2][2])(EmulateSpecStruct*) =
 {
  //DebugMode=false  DebugMode=true
  { RunLoop<false>, RLTDAT(false) },	// EmulateICache=false
  { RunLoop<true>,  RLTDAT(true)  },	// EmulateICache=true
 };
#undef RLTDAT
 end_ts = rltab[NeedEmuICache][DBG_NeedCPUHooks()](espec);
 assert(end_ts >= 0);

 ForceEventUpdates(end_ts);
 //
 SMPC_EndFrame(espec, end_ts);
 //
 //
 //
 RebaseTS(end_ts);

 CDB_ResetTS();
 SOUND_AdjustTS(-end_ts);
 VDP1::AdjustTS(-end_ts);
 VDP2::AdjustTS(-end_ts);
 SMPC_ResetTS();
 SCU_AdjustTS(-end_ts);
 CART_AdjustTS(-end_ts);

 UpdateInputLastBigTS -= (int64)end_ts * cur_clock_div * 1000 * 1000;
 //
 SH7095_mem_timestamp -= end_ts; // Update before CPU[n].AdjustTS()
 //
 for(unsigned c = 0; c < 2; c++)
  CPU[c].AdjustTS(-end_ts);

 //printf("B=% 7d M=% 7d S=% 7d\n", SH7095_mem_timestamp, CPU[0].timestamp, CPU[1].timestamp);
 //
 //
 //
 espec->MasterCycles = end_ts * cur_clock_div;
 espec->SoundBufSize += SOUND_FlushOutput();
 espec->NeedSoundReverse = false;

 SMPC_UpdateOutput();
 //
 //
 //
 if(BackupRAM_Dirty)
 {
  BackupRAM_SaveDelay = (int64)3 * (EmulatedSS.MasterClock / MDFN_MASTERCLOCK_FIXED(1));  // 3 second delay
  BackupRAM_Dirty = false;
 }
 else if(BackupRAM_SaveDelay > 0)
 {
  BackupRAM_SaveDelay -= espec->MasterCycles;

  if(BackupRAM_SaveDelay <= 0)
  {
   try
   {
    SaveBackupRAM();
   }
   catch(std::exception& e)
   {
    MDFN_DispMessage("%s", e.what());
    BackupRAM_SaveDelay = (int64)60 * (EmulatedSS.MasterClock / MDFN_MASTERCLOCK_FIXED(1));  // 60 second retry delay.
   }
  }
 }

 if(CART_GetClearNVDirty())
  CartNV_SaveDelay = (int64)3 * (EmulatedSS.MasterClock / MDFN_MASTERCLOCK_FIXED(1));  // 3 second delay
 else if(CartNV_SaveDelay > 0)
 {
  CartNV_SaveDelay -= espec->MasterCycles;

  if(CartNV_SaveDelay <= 0)
  {
   try
   {
    SaveCartNV();
   }
   catch(std::exception& e)
   {
    MDFN_DispMessage("%s", e.what());
    CartNV_SaveDelay = (int64)60 * (EmulatedSS.MasterClock / MDFN_MASTERCLOCK_FIXED(1));  // 60 second retry delay.
   }
  }
 }
}

//
//
//

static MDFN_COLD void Cleanup(void)
{
 CART_Kill();

#ifdef HAVE_DEBUG
 DBG_Kill();
#endif
 VDP1::Kill();
 VDP2::Kill();
 SOUND_Kill();
 CDB_Kill();

 disc_cleanup();
}

typedef struct
{
   const unsigned type;
   const char *name;
} CartName;

bool MDFN_COLD InitCommon(const unsigned cpucache_emumode, const unsigned horrible_hacks, const unsigned cart_type, const unsigned smpc_area)
{
#ifdef MDFN_ENABLE_DEV_BUILD
 ss_dbg_mask = SS_DBG_ERROR;
 {
  std::vector<uint64> dms = MDFN_GetSettingMultiUI("ss.dbg_mask");

  for(uint64 dmse : dms)
   ss_dbg_mask |= dmse;
 }
#endif
 //

   unsigned i;
 //
 {
  const struct
  {
   unsigned mode;
   const char* name;
  } CPUCacheEmuModes[] =
  {
   { CPUCACHE_EMUMODE_DATA_CB,   _("Data only, with high-level bypass") },
   { CPUCACHE_EMUMODE_DATA,   _("Data only") },
   { CPUCACHE_EMUMODE_FULL,   _("Full") },
  };
  const char* cem = _("Unknown");

  for(auto const& ceme : CPUCacheEmuModes)
  {
   if(ceme.mode == cpucache_emumode)
   {
    cem = ceme.name;
    break;
   }
  }
  log_cb(RETRO_LOG_INFO, "[Mednafen]: CPU Cache Emulation Mode: %s\n", cem);
 }
 //
 if(horrible_hacks)
  log_cb(RETRO_LOG_INFO, "[Mednafen]: Horrible hacks: 0x%08x\n", horrible_hacks);
 //
   {
      log_cb(RETRO_LOG_INFO, "[Mednafen]: Region: 0x%01x.\n", smpc_area);
      const CartName CartNames[] =
      {
         { CART_NONE, "None" },
         { CART_BACKUP_MEM, "Backup Memory" },
         { CART_EXTRAM_1M, "1MiB Extended RAM" },
         { CART_EXTRAM_4M, "4MiB Extended RAM" },
         { CART_KOF95, "King of Fighters '95 ROM" },
         { CART_ULTRAMAN, "Ultraman ROM" },
         { CART_CS1RAM_16M, _("16MiB CS1 RAM") },
         { CART_NLMODEM, _("Netlink Modem") },
         { CART_MDFN_DEBUG, "Mednafen Debug" }
      };
      const char* cn = nullptr;

      for(i = 0; i < ARRAY_SIZE(CartNames); i++)
      {
         CartName cne = CartNames[i];
         if(cne.type != cart_type)
            continue;
         cn = cne.name;
         break;
      }
      if ( cn ) {
         log_cb(RETRO_LOG_INFO, "[Mednafen]: Cart: %s.\n", cn);
     } else {
         log_cb(RETRO_LOG_INFO, "[Mednafen]: Cart: Unknown (%d).\n", cart_type );
     }
   }
   //

   NeedEmuICache = (cpucache_emumode == CPUCACHE_EMUMODE_FULL);
   for(i = 0; i < 2; i++)
   {
      CPU[i].Init((cpucache_emumode == CPUCACHE_EMUMODE_FULL), (cpucache_emumode == CPUCACHE_EMUMODE_DATA_CB));
      CPU[i].SetMD5((bool)i);
   }
 SH7095_mem_timestamp = 0;
 SH7095_DB = 0;

 ss_horrible_hacks = horrible_hacks;

   //
   // Initialize backup memory.
   //
   memset(BackupRAM, 0x00, sizeof(BackupRAM));
   for(i = 0; i < 0x40; i++)
      BackupRAM[i] = BRAM_Init_Data[i & 0x0F];

   // Call InitFastMemMap() before functions like SOUND_Init()
   InitFastMemMap();
   SS_SetPhysMemMap(0x00000000, 0x000FFFFF, BIOSROM, sizeof(BIOSROM));
   SS_SetPhysMemMap(0x00200000, 0x003FFFFF, WorkRAML, WORKRAM_BANK_SIZE_BYTES, true);
   SS_SetPhysMemMap(0x06000000, 0x07FFFFFF, WorkRAMH, WORKRAM_BANK_SIZE_BYTES, true);
   MDFNMP_RegSearchable(0x00200000, WORKRAM_BANK_SIZE_BYTES);
   MDFNMP_RegSearchable(0x06000000, WORKRAM_BANK_SIZE_BYTES);

   CART_Init(cart_type);
  ActiveCartType = cart_type;

   //
   //
   //
   const bool PAL = is_pal = (smpc_area & SMPC_AREA__PAL_MASK);
   const int32 MasterClock = PAL ? 1734687500 : 1746818182; // NTSC: 1746818181.8181818181, PAL: 1734687500-ish
   const char* bios_filename;
   int sls = MDFN_GetSettingI(PAL ? "ss.slstartp" : "ss.slstart");
   int sle = MDFN_GetSettingI(PAL ? "ss.slendp" : "ss.slend");
 const uint64 vdp2_affinity = 0; /*LibRetro: unused*/

   if(sls > sle)
      std::swap(sls, sle);

   if(smpc_area == SMPC_AREA_JP || smpc_area == SMPC_AREA_ASIA_NTSC)
      bios_filename = "sega_101.bin"; // Japan
   else
      bios_filename = "mpr-17933.bin"; // North America and Europe

   {
      char bios_path[4096];
      snprintf(bios_path, sizeof(bios_path), "%s" RETRO_SLASH "%s", retro_base_directory, bios_filename);

      RFILE *BIOSFile = filestream_open(bios_path,
            RETRO_VFS_FILE_ACCESS_READ,
            RETRO_VFS_FILE_ACCESS_HINT_NONE);

      if(!BIOSFile)
      {
         log_cb(RETRO_LOG_ERROR, "Cannot open BIOS file \"%s\".\n", bios_path);
         return false;
      }
      else if(filestream_get_size(BIOSFile) != 524288)
      {
         log_cb(RETRO_LOG_ERROR, "BIOS file \"%s\" is of an incorrect size.\n", bios_path);
         return false;
      }
      else
      {
         filestream_read(BIOSFile, BIOSROM, 512 * 1024);
         filestream_close(BIOSFile);
         BIOS_SHA256 = sha256(BIOSROM, 512 * 1024);

         // swap endian-ness
         for(unsigned i = 0; i < 262144; i++)
            BIOSROM[i] = MDFN_de16msb((const uint8_t*)&BIOSROM[i]);
      }
   }

   EmulatedSS.MasterClock = MDFN_MASTERCLOCK_FIXED(MasterClock);

   SCU_Init();
   SMPC_Init(smpc_area, MasterClock);
   VDP1::Init();
   VDP2::Init(PAL,vdp2_affinity);
   VDP2::SetGetVideoParams(&EmulatedSS, true, sls, sle, true, DoHBlend);
   CDB_Init();
   SOUND_Init();

   InitEvents();
   UpdateInputLastBigTS = 0;

#ifdef HAVE_DEBUG
   DBG_Init();
#endif

   // Apply multi-tap state to SMPC
   SMPC_SetMultitap( 0, setting_multitap_port1 );
   SMPC_SetMultitap( 1, setting_multitap_port2 );

   /*for(unsigned vp = 0; vp < 12; vp++)
   {
      char buf[64];
      uint32 sv;

      snprintf(buf, sizeof(buf), "ss.input.port%u.gun_chairs", vp + 1);
      sv = MDFN_GetSettingUI(buf);
      SMPC_SetCrosshairsColor(vp, sv);
   }*/
   //
   //
   //

   try { LoadRTC();       } catch(MDFN_Error& e) { if(e.GetErrno() != ENOENT) throw; }
   try { LoadBackupRAM(); } catch(MDFN_Error& e) { if(e.GetErrno() != ENOENT) throw; }
   try { LoadCartNV();    } catch(MDFN_Error& e) { if(e.GetErrno() != ENOENT) throw; }

   BackupBackupRAM();
   BackupCartNV();

   BackupRAM_Dirty = false;
   BackupRAM_SaveDelay = 0;

   CART_GetClearNVDirty();
   CartNV_SaveDelay = 0;
   //
   if(MDFN_GetSettingB("ss.smpc.autortc"))
   {
      time_t ut;
      struct tm* ht;

      if((ut = time(NULL)) == (time_t)-1)
      {
         log_cb(RETRO_LOG_ERROR,
               "AutoRTC error #1\n");
         return false;
      }

      if((ht = localtime(&ut)) == NULL)
      {
         log_cb(RETRO_LOG_ERROR,
               "AutoRTC error #2\n");
         return false;
      }

      SMPC_SetRTC(ht, MDFN_GetSettingUI("ss.smpc.autortc.lang"));
   }
   //
   SS_Reset(true);

   return true;
}

MDFN_COLD void CloseGame(void)
{
#ifdef MDFN_ENABLE_DEV_BUILD
 VDP1::MakeDump("/tmp/vdp1_dump.h");
 VDP2::MakeDump("/tmp/vdp2_dump.h");
#endif
 //
 //

 SaveBackupRAM();
 SaveCartNV();
 SaveRTC();

 Cleanup();
}

void MDFN_BackupSavFile(const uint8 max_backup_count, const char* sav_ext)
{
   // stub for libretro port
}

static MDFN_COLD void SaveBackupRAM(void)
{
 FileStream brs(MDFN_MakeFName(MDFNMKF_SAV, 0, "bkr"), MODE_WRITE_INPLACE);

 brs.write(BackupRAM, sizeof(BackupRAM));

 brs.close();
}

static MDFN_COLD void LoadBackupRAM(void)
{
 RFILE *brs = filestream_open(MDFN_MakeFName(MDFNMKF_SAV, 0, "bkr"),
       RETRO_VFS_FILE_ACCESS_READ,
       RETRO_VFS_FILE_ACCESS_HINT_NONE);

 if (!brs)
    return;

 filestream_read(brs, BackupRAM, sizeof(BackupRAM));
 filestream_close(brs);
}

static MDFN_COLD void BackupBackupRAM(void)
{
 MDFN_BackupSavFile(10, "bkr");
}

static MDFN_COLD void BackupCartNV(void)
{
 const char* ext = nullptr;
 void* nv_ptr = nullptr;
 bool nv16 = false;
 uint64 nv_size = 0;

 CART_GetNVInfo(&ext, &nv_ptr, &nv16, &nv_size);

 if(ext)
  MDFN_BackupSavFile(10, ext);
}

static MDFN_COLD void LoadCartNV(void)
{
   uint64_t i;
   RFILE *nvs      = NULL;
   const char* ext = nullptr;
   void* nv_ptr    = nullptr;
   bool nv16       = false;
   uint64 nv_size  = 0;

   CART_GetNVInfo(&ext, &nv_ptr, &nv16, &nv_size);

   if (!ext)
      return;

   nvs = filestream_open(
         MDFN_MakeFName(MDFNMKF_SAV, 0, ext),
         RETRO_VFS_FILE_ACCESS_READ,
         RETRO_VFS_FILE_ACCESS_HINT_NONE);

   if (!nvs)
      return;

   filestream_read(nvs, nv_ptr, nv_size);
   filestream_close(nvs);

   if (!nv16)
      return;

   for(i = 0; i < nv_size; i += 2)
   {
      void* p = (uint8*)nv_ptr + i;

      MDFN_ennsb<uint16>(p, MDFN_de16msb(p));
   }
}

static MDFN_COLD void SaveCartNV(void)
{
   const char* ext = nullptr;
   void* nv_ptr = nullptr;
   bool nv16 = false;
   uint64 nv_size = 0;

   CART_GetNVInfo(&ext, &nv_ptr, &nv16, &nv_size);

   if(ext)
   {
      FileStream nvs(MDFN_MakeFName(MDFNMKF_SAV, 0, ext), MODE_WRITE_INPLACE);

      if(nv16)
      {
         uint64_t i;
         /* Slow... */
         for(i = 0; i < nv_size; i += 2)
            nvs.put_BE<uint16>(MDFN_densb<uint16>((uint8*)nv_ptr + i));
      }
      else
         nvs.write(nv_ptr, nv_size);

      nvs.close();
   }
}

static MDFN_COLD void SaveRTC(void)
{
   FileStream sds(MDFN_MakeFName(MDFNMKF_SAV, 0, "smpc"), MODE_WRITE_INPLACE);

   SMPC_SaveNV(&sds);

   sds.close();
}

static MDFN_COLD void LoadRTC(void)
{
   FileStream sds(MDFN_MakeFName(MDFNMKF_SAV, 0, "smpc"), MODE_READ);

   SMPC_LoadNV(&sds);
}

struct EventsPacker
{
 enum : size_t { eventcopy_first = SS_EVENT__SYNFIRST + 1 };
 enum : size_t { eventcopy_bound = SS_EVENT__SYNLAST };

 bool Restore(const unsigned state_version);
 void Save(void);

 int32 event_times[eventcopy_bound - eventcopy_first];
 uint8 event_order[eventcopy_bound - eventcopy_first];
};

INLINE void EventsPacker::Save(void)
{
 event_list_entry* evt = events[SS_EVENT__SYNFIRST].next;

 for(size_t i = eventcopy_first; i < eventcopy_bound; i++)
 {
  event_times[i - eventcopy_first] = events[i].event_time;
  event_order[i - eventcopy_first] = evt - events;
  assert(event_order[i - eventcopy_first] >= eventcopy_first && event_order[i - eventcopy_first] < eventcopy_bound);
  evt = evt->next;
 }
}

INLINE bool EventsPacker::Restore(const unsigned state_version)
{
 bool used[SS_EVENT__COUNT] = { 0 };
 event_list_entry* evt = &events[SS_EVENT__SYNFIRST];
 for(size_t i = eventcopy_first; i < eventcopy_bound; i++)
 {
  int32 et = event_times[i - eventcopy_first];
  uint8 eo = event_order[i - eventcopy_first];

  if(state_version < 0x00102600 && et >= 0x40000000)
  {
   et = SS_EVENT_DISABLED_TS;
  }

  if(eo < eventcopy_first || eo >= eventcopy_bound)
   return false;

  if(used[eo])
   return false;

  used[eo] = true;

  if(et < events[SS_EVENT__SYNFIRST].event_time)
   return false;

  events[i].event_time = et;

  evt->next = &events[eo];
  evt->next->prev = evt;
  evt = evt->next;
 }
 evt->next = &events[SS_EVENT__SYNLAST];
 evt->next->prev = evt;

 for(size_t i = 0; i < SS_EVENT__COUNT; i++)
 {
  if(i == SS_EVENT__SYNLAST)
  {
   if(events[i].next != NULL)
    return false;
  }
  else
  {
   if(events[i].next->prev != &events[i])
    return false;

   if(events[i].next->event_time < events[i].event_time)
    return false;
  }

  if(i == SS_EVENT__SYNFIRST)
  {
   if(events[i].prev != NULL)
    return false;
  }
  else
  {
   if(events[i].prev->next != &events[i])
    return false;

   if(events[i].prev->event_time > events[i].event_time)
    return false;
  }
 }

 return true;
}

MDFN_COLD int LibRetro_StateAction( StateMem* sm, const unsigned load, const bool data_only )
{
   if (!data_only)
   {
      sha256_digest sr_dig = BIOS_SHA256;
      int cart_type = ActiveCartType;

      SFORMAT SRDStateRegs[] =
      {
         SFPTR8( sr_dig.data(), sr_dig.size() ),
         SFVAR(cart_type),
         SFEND
      };

      if (MDFNSS_StateAction( sm, load, data_only, SRDStateRegs, "BIOS_HASH", true ) == 0)
         return 0;

      if ( load )
      {
		 if ( sr_dig != BIOS_SHA256 ) {
           log_cb( RETRO_LOG_WARN, "BIOS hash mismatch(save state created under a different BIOS)!\n" );
           return 0;
         }
         if ( cart_type != ActiveCartType ) {
           log_cb( RETRO_LOG_WARN, "Cart type mismatch(save state created with a different cart)!\n" );
           return 0;
         }
      }
   }
 //
 //
 //
 bool RecordedNeedEmuICache = load ? false : NeedEmuICache;
 EventsPacker ep;
 ep.Save();

 SFORMAT StateRegs[] =
 {
  // cur_clock_div
  SFVAR(UpdateInputLastBigTS),

  SFVAR(next_event_ts),
  SFPTR32N(ep.event_times, sizeof(ep.event_times) / sizeof(ep.event_times[0]), "event_times"),
  SFPTR8N(ep.event_order, sizeof(ep.event_order) / sizeof(ep.event_order[0]), "event_order"),

  SFVAR(SH7095_mem_timestamp),
  SFVAR(SH7095_BusLock),
  SFVAR(SH7095_DB),

  SFPTR16(WorkRAML, WORKRAM_BANK_SIZE_BYTES / sizeof(uint16_t)),
  SFPTR16(WorkRAMH, WORKRAM_BANK_SIZE_BYTES / sizeof(uint16_t)),
  SFPTR8(BackupRAM, sizeof(BackupRAM) / sizeof(BackupRAM[0])),

  SFVAR(RecordedNeedEmuICache),

  SFEND
 };

 CPU[0].StateAction(sm, load, data_only, "SH2-M");
 CPU[1].StateAction(sm, load, data_only, "SH2-S");
 SCU_StateAction(sm, load, data_only);
 SMPC_StateAction(sm, load, data_only);

 CDB_StateAction(sm, load, data_only);
 VDP1::StateAction(sm, load, data_only);
 VDP2::StateAction(sm, load, data_only);

 SOUND_StateAction(sm, load, data_only);
 CART_StateAction(sm, load, data_only);
 //
   if (MDFNSS_StateAction(sm, load, data_only, StateRegs, "MAIN", false) == 0)
   {
      log_cb( RETRO_LOG_ERROR, "Failed to load MAIN state objects.\n" );
      return 0;
   }

   if (input_StateAction( sm, load, data_only ) == 0)
   {
      log_cb( RETRO_LOG_WARN, "Input state failed.\n" );
   }

   if ( load )
   {
      BackupRAM_Dirty = true;

      if ( !ep.Restore(load) )
      {
         log_cb( RETRO_LOG_WARN, "Bad state events data.\n" );
         InitEvents();
      }

         
      CPU[0].PostStateLoad(load, RecordedNeedEmuICache, NeedEmuICache);
      CPU[1].PostStateLoad(load, RecordedNeedEmuICache, NeedEmuICache);
   }

   // Success!
   return 1;
}

static const MDFNSetting_EnumList RTCLang_List[] =
{
 { "english", SMPC_RTC_LANG_ENGLISH, "English" },
 { "german", SMPC_RTC_LANG_GERMAN, "Deutsch" },
 { "french", SMPC_RTC_LANG_FRENCH, "Français" },
 { "spanish", SMPC_RTC_LANG_SPANISH, "Español" },
 { "italian", SMPC_RTC_LANG_ITALIAN, "Italiano" },
 { "japanese", SMPC_RTC_LANG_JAPANESE, "日本語" },

 { "deutsch", SMPC_RTC_LANG_GERMAN, NULL },
 { "français", SMPC_RTC_LANG_FRENCH, NULL },
 { "español", SMPC_RTC_LANG_SPANISH, NULL },
 { "italiano", SMPC_RTC_LANG_ITALIAN, NULL },
 { "日本語", SMPC_RTC_LANG_JAPANESE, NULL},

 { NULL, 0 },
};

static MDFNSetting SSSettings[] =
{
 { "ss.scsp.resamp_quality", MDFNSF_NOFLAGS, "SCSP output resampler quality.",
   "0 is lowest quality and CPU usage, 10 is highest quality and CPU usage.  The resampler that this setting refers to is used for converting from 44.1KHz to the sampling rate of the host audio device Mednafen is using.  Changing Mednafen's output rate, via the \"sound.rate\" setting, to \"44100\" may bypass the resampler, which can decrease CPU usage by Mednafen, and can increase or decrease audio quality, depending on various operating system and hardware factors.", MDFNST_UINT, "4", "0", "10" },

 { "ss.input.port1.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 1.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0xFF0000", "0x000000", "0x1000000" },
 { "ss.input.port2.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 2.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0x00FF00", "0x000000", "0x1000000" },
 { "ss.input.port3.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 3.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0xFF00FF", "0x000000", "0x1000000" },
 { "ss.input.port4.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 4.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0xFF8000", "0x000000", "0x1000000" },
 { "ss.input.port5.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 5.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0xFFFF00", "0x000000", "0x1000000" },
 { "ss.input.port6.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 6.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0x00FFFF", "0x000000", "0x1000000" },
 { "ss.input.port7.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 7.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0x0080FF", "0x000000", "0x1000000" },
 { "ss.input.port8.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 8.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0x8000FF", "0x000000", "0x1000000" },
 { "ss.input.port9.gun_chairs",  MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 9.",  "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0xFF80FF", "0x000000", "0x1000000" },
 { "ss.input.port10.gun_chairs", MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 10.", "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0x00FF80", "0x000000", "0x1000000" },
 { "ss.input.port11.gun_chairs", MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 11.", "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0x8080FF", "0x000000", "0x1000000" },
 { "ss.input.port12.gun_chairs", MDFNSF_NOFLAGS, "Crosshairs color for lightgun on virtual port 12.", "A value of 0x1000000 disables crosshair drawing.", MDFNST_UINT, "0xFF8080", "0x000000", "0x1000000" },



 { "ss.smpc.autortc", MDFNSF_NOFLAGS, "Automatically set RTC on game load.", "Automatically set the SMPC's emulated Real-Time Clock to the host system's current time and date upon game load.", MDFNST_BOOL, "1" },
 { "ss.smpc.autortc.lang", MDFNSF_NOFLAGS, "BIOS language.", NULL, MDFNST_ENUM, "english", NULL, NULL, NULL, NULL, RTCLang_List },

 { "ss.cart.kof95_path", MDFNSF_EMU_STATE, "Path to KoF 95 ROM image.", NULL, MDFNST_STRING, "mpr-18811-mx.ic1" },
 { "ss.cart.ultraman_path", MDFNSF_EMU_STATE, "Path to Ultraman ROM image.", NULL, MDFNST_STRING, "mpr-19367-mx.ic1" },
 { "ss.cart.satar4mp_path", MDFNSF_EMU_STATE | MDFNSF_SUPPRESS_DOC | MDFNSF_NONPERSISTENT, "Path to Action Replay 4M Plus firmware image.", NULL, MDFNST_STRING, "satar4mp.bin" },

 // { "ss.cart.modem_port", MDFNSF_NOFLAGS, "TCP/IP port to use for modem emulation.", "A value of \"0\" disables network access.", MDFNST_UINT, "4920", "0", "65535" },

 { "ss.bios_sanity", MDFNSF_NOFLAGS, "Enable BIOS ROM image sanity checks.", NULL, MDFNST_BOOL, "1" },

 { "ss.slstart", MDFNSF_NOFLAGS, "First displayed scanline in NTSC mode.", NULL, MDFNST_INT, "0", "0", "239" },
 { "ss.slend", MDFNSF_NOFLAGS, "Last displayed scanline in NTSC mode.", NULL, MDFNST_INT, "239", "0", "239" },

 { "ss.slstartp", MDFNSF_NOFLAGS, "First displayed scanline in PAL mode.", NULL, MDFNST_INT, "0", "-16", "271" },
 { "ss.slendp", MDFNSF_NOFLAGS, "Last displayed scanline in PAL mode.", NULL, MDFNST_INT, "255", "-16", "271" },

#ifdef MDFN_ENABLE_DEV_BUILD
 { "ss.dbg_mask", MDFNSF_NOFLAGS, "Debug printf mask.", NULL, MDFNST_UINT, "0x00001", "0x00000", "0xFFFFF" },
 { "ss.dbg_exe_cdpath", MDFNSF_SUPPRESS_DOC, "CD image to use with homebrew executable loading.", NULL, MDFNST_STRING, "" },
#endif

 { NULL },
};

static const CheatInfoStruct CheatInfo =
{
 NULL,
 NULL,

 CheatMemRead,
 CheatMemWrite,

 CheatFormatInfo_Empty,

 true
};

MDFNGI EmulatedSS =
{
   SSSettings,
   0,
   0,

   true, // Multires possible?

   //
   // Note: Following video settings will be overwritten during game load.
   //
   320,  // lcm_width
   240,  // lcm_height
   NULL,  // Dummy

   320,   // Nominal width
   240,   // Nominal height

   0,   // Framebuffer width
   0,   // Framebuffer height
   //
   //
   //

   2,     // Number of output sound channels
};
