#ifndef __MDFN_GIT_H
#define __MDFN_GIT_H

#include <algorithm>
#include <string>
#include <vector>
#include <map>
#include <libretro.h>

#include "video/surface.h"

typedef struct
{
 const char *extension; // Example ".nes"
 const char *description; // Example "iNES Format ROM Image"
} FileExtensionSpecStruct;

typedef enum
{
 VIDSYS_NONE, // Can be used internally in system emulation code, but it is an error condition to let it continue to be
	      // after the Load() or LoadCD() function returns!
 VIDSYS_PAL,
 VIDSYS_PAL_M, // Same timing as NTSC, but uses PAL-style colour encoding
 VIDSYS_NTSC,
 VIDSYS_SECAM
} VideoSystems;

#include "state.h"
#include "settings-common.h"

enum InputDeviceInputType : uint8
{
 IDIT_PADDING = 0,	// n-bit, zero

 IDIT_BUTTON,		// 1-bit
 IDIT_BUTTON_CAN_RAPID, // 1-bit

 IDIT_SWITCH,		// ceil(log2(n))-bit
			// Current switch position(default 0).
			// Persistent, and bidirectional communication(can be modified driver side, and Mednafen core and emulation module side)

 IDIT_STATUS,		// ceil(log2(n))-bit
			// emulation module->driver communication

 IDIT_AXIS,		// 16-bits; 0 through 65535; 32768 is centered position

 IDIT_POINTER_X,	// mouse pointer, 16-bits, signed - in-screen/window range before scaling/offseting normalized coordinates: [0.0, 1.0)
 IDIT_POINTER_Y,	// see: mouse_scale_x, mouse_scale_y, mouse_offs_x, mouse_offs_y

 IDIT_AXIS_REL,		// mouse relative motion, 16-bits, signed

 IDIT_BYTE_SPECIAL,

 IDIT_RESET_BUTTON,	// 1-bit

 IDIT_BUTTON_ANALOG,	// 16-bits, 0 - 65535

 IDIT_RUMBLE,		// 16-bits, lower 8 bits are weak rumble(0-255), next 8 bits are strong rumble(0-255), 0=no rumble, 255=max rumble.  Somewhat subjective, too...
			// It's a rather special case of game module->driver code communication.
};


enum : uint8
{
 IDIT_AXIS_FLAG_SQLR		= 0x01,	// Denotes analog data that may need to be scaled to ensure a more squareish logical range(for emulated analog sticks).
 IDIT_AXIS_FLAG_INVERT_CO	= 0x02,	// Invert config order of the two components(neg,pos) of the axis.
 IDIT_AXIS_REL_FLAG_INVERT_CO 	= IDIT_AXIS_FLAG_INVERT_CO,
 IDIT_FLAG_AUX_SETTINGS_UNDOC	= 0x80,
};

struct IDIIS_StatusState
{
	const char* ShortName;
	const char* Name;
	int32 Color;	// (msb)0RGB(lsb), -1 for unused.
};

struct IDIIS_SwitchPos
{
	const char* SettingName;
	const char* Name;
	const char* Description;
};

struct InputDeviceInputInfoStruct
{
	const char *SettingName;	// No spaces, shouldbe all a-z0-9 and _. Definitely no ~!
	const char *Name;
        int16 ConfigOrder;          	// Configuration order during in-game config process, -1 for no config.
	InputDeviceInputType Type;

	uint8 Flags;
	uint8 BitSize;
	uint16 BitOffset;

	union
	{
	 struct
	 {
	  const char *ExcludeName;	// SettingName of a button that can't be pressed at the same time as this button
					// due to physical limitations.
	 } Button;
	 //
	 //
	 //
	 struct
	 {
	  const char* sname_dir[2];
	  const char* name_dir[2];
	 } Axis;

	 struct
	 {
	  const char* sname_dir[2];
	  const char* name_dir[2];
	 } AxisRel;

         struct
         {
	  const IDIIS_SwitchPos* Pos;
	  uint32 NumPos;
	  uint32 DefPos;
         } Switch;

	 struct
	 {
	  const IDIIS_StatusState* States;
	  uint32 NumStates;
	 } Status;
	};
};

struct IDIISG : public std::vector<InputDeviceInputInfoStruct>
{
 IDIISG();
 IDIISG(std::initializer_list<InputDeviceInputInfoStruct> l);
 uint32 InputByteSize;
};

MDFN_HIDE extern const IDIISG IDII_Empty;

static INLINE constexpr InputDeviceInputInfoStruct IDIIS_Button(const char* sname, const char* name, int16 co, const char* exn = nullptr)
{
 return { sname, name, co, IDIT_BUTTON, 0, 0, 0, { { exn } } };
}

static INLINE constexpr InputDeviceInputInfoStruct IDIIS_ButtonCR(const char* sname, const char* name, int16 co, const char* exn = nullptr)
{
 return { sname, name, co, IDIT_BUTTON_CAN_RAPID, 0, 0, 0, { { exn } } };
}

static INLINE constexpr InputDeviceInputInfoStruct IDIIS_AnaButton(const char* sname, const char* name, int16 co)
{
 return { sname, name, co, IDIT_BUTTON_ANALOG, 0, 0, 0 };
}

static INLINE constexpr InputDeviceInputInfoStruct IDIIS_Rumble(const char* sname = "rumble", const char* name = "Rumble")
{
 return { sname, name, -1, IDIT_RUMBLE, 0, 0, 0 };
}

static INLINE constexpr InputDeviceInputInfoStruct IDIIS_ResetButton(void)
{
 return { nullptr, nullptr, -1, IDIT_RESET_BUTTON, 0, 0, 0 };
}

template<unsigned nbits = 1>
static INLINE constexpr InputDeviceInputInfoStruct IDIIS_Padding(void)
{
 return { nullptr, nullptr, -1, IDIT_PADDING, 0, nbits, 0 };
}

static INLINE /*constexpr*/ InputDeviceInputInfoStruct IDIIS_Axis(const char* sname_pfx, const char* name_pfx, const char* sname_neg, const char* name_neg, const char* sname_pos, const char* name_pos, int16 co, bool co_invert = false, bool sqlr = false)
{
 InputDeviceInputInfoStruct ret = { sname_pfx, name_pfx, co, IDIT_AXIS, (uint8)((sqlr ? IDIT_AXIS_FLAG_SQLR : 0) | (co_invert ? IDIT_AXIS_FLAG_INVERT_CO : 0)), 0, 0 };

 ret.Axis.sname_dir[0] = sname_neg;
 ret.Axis.sname_dir[1] = sname_pos;
 ret.Axis.name_dir[0] = name_neg;
 ret.Axis.name_dir[1] = name_pos;

 return ret;
}

static INLINE /*constexpr*/ InputDeviceInputInfoStruct IDIIS_AxisRel(const char* sname_pfx, const char* name_pfx, const char* sname_neg, const char* name_neg, const char* sname_pos, const char* name_pos, int16 co, bool co_invert = false, bool sqlr = false)
{
 InputDeviceInputInfoStruct ret = { sname_pfx, name_pfx, co, IDIT_AXIS_REL, (uint8)(co_invert ? IDIT_AXIS_REL_FLAG_INVERT_CO : 0), 0, 0 };

 ret.AxisRel.sname_dir[0] = sname_neg;
 ret.AxisRel.sname_dir[1] = sname_pos;
 ret.AxisRel.name_dir[0] = name_neg;
 ret.AxisRel.name_dir[1] = name_pos;

 return ret;
}

template<uint32 spn_count, uint32 defpos = 0>
static INLINE /*constexpr*/ InputDeviceInputInfoStruct IDIIS_Switch(const char* sname, const char* name, int16 co, const IDIIS_SwitchPos (&spn)[spn_count], const bool undoc_defpos_setting = true)
{
 InputDeviceInputInfoStruct ret = { sname, name, co, IDIT_SWITCH, (uint8)(undoc_defpos_setting ? IDIT_FLAG_AUX_SETTINGS_UNDOC : 0), 0, 0 };

 static_assert(defpos < spn_count, "Invalid default switch position!");

 ret.Switch.Pos = spn;
 ret.Switch.NumPos = spn_count;
 ret.Switch.DefPos = defpos;

 return ret;
}

template<uint32 ss_count>
static INLINE /*constexpr*/ InputDeviceInputInfoStruct IDIIS_Status(const char* sname, const char* name, const IDIIS_StatusState (&ss)[ss_count])
{
 InputDeviceInputInfoStruct ret = { sname, name, -1, IDIT_STATUS, 0, 0, 0 };

 ret.Status.States = ss;
 ret.Status.NumStates = ss_count;

 return ret;
}

struct InputDeviceInfoStruct
{
 const char *ShortName;
 const char *FullName;
 const char *Description;

 const IDIISG& IDII;

 unsigned Flags;

 enum
 {
  FLAG_KEYBOARD = (1U << 0)
 };
};

struct InputPortInfoStruct
{
 const char *ShortName;
 const char *FullName;
 const std::vector<InputDeviceInfoStruct> &DeviceInfo;
 const char *DefaultDevice;	// Default device for this port.
};

struct MemoryPatch;

struct CheatFormatStruct
{
 const char *FullName;		//"Game Genie", "GameShark", "Pro Action Catplay", etc.
 const char *Description;	// Whatever?

 bool (*DecodeCheat)(const std::string& cheat_string, MemoryPatch* patch);	// *patch should be left as initialized by MemoryPatch::MemoryPatch(), unless this is the
										// second(or third or whatever) part of a multipart cheat.
										//
										// Will throw an std::exception(or derivative) on format error.
										//
										// Will return true if this is part of a multipart cheat.
};

MDFN_HIDE extern const std::vector<CheatFormatStruct> CheatFormatInfo_Empty;

struct CheatInfoStruct
{
 //
 // InstallReadPatch and RemoveReadPatches should be non-NULL(even if only pointing to dummy functions) if the emulator module supports
 // read-substitution and read-substitution-with-compare style(IE Game Genie-style) cheats.
 //
 // See also "SubCheats" global stuff in mempatcher.h.
 //
 void (*InstallReadPatch)(uint32 address, uint8 value, int compare); // Compare is >= 0 when utilized.
 void (*RemoveReadPatches)(void);
 uint8 (*MemRead)(uint32 addr);
 void (*MemWrite)(uint32 addr, uint8 val);

 const std::vector<CheatFormatStruct>& CheatFormatInfo;

 bool BigEndian;	// UI default for cheat search and new cheats.
};

MDFN_HIDE extern const CheatInfoStruct CheatInfo_Empty;

// Miscellaneous system/simple commands(power, reset, dip switch toggles, coin insert, etc.)
// (for DoSimpleCommand() )
enum
{
 MDFN_MSC_RESET = 0x01,
 MDFN_MSC_POWER = 0x02,
 MDFN_MSC__LAST = 0x3F	// WARNING: Increasing(or having the enum'd value of a command greater than this :b) this will necessitate a change to the netplay protocol.
};

struct EmulateSpecStruct
{
	// Pitch(32-bit) must be equal to width and >= the "fb_width" specified in the MDFNGI struct for the emulated system.
	// Height must be >= to the "fb_height" specified in the MDFNGI struct for the emulated system.
	// The framebuffer pointed to by surface->pixels is written to by the system emulation code.
	MDFN_Surface* surface = nullptr;

	// Set by the system emulation code every frame, to denote the horizontal and vertical offsets of the image, and the size
	// of the image.  If the emulated system sets the elements of LineWidths, then the width(w) of this structure
	// is ignored while drawing the image.
	MDFN_Rect DisplayRect = { 0, 0, 0, 0 };

	// Pointer to an array of int32, number of elements = fb_height, set by the driver code.  Individual elements written
	// to by system emulation code.  If the emulated system doesn't support multiple screen widths per frame, or if you handle
	// such a situation by outputting at a constant width-per-frame that is the least-common-multiple of the screen widths, then
	// you can ignore this.  If you do wish to use this, you must set all elements every frame.
	int32 *LineWidths = nullptr;

	// Set(optionally) by emulation code.  If InterlaceOn is true, then assume field height is 1/2 DisplayRect.h, and
	// only every other line in surface (with the start line defined by InterlacedField) has valid data
	// (it's up to internal Mednafen code to deinterlace it).
	bool InterlaceOn = false;
	bool InterlaceField = false;

	// Skip rendering this frame if true.  Set by the driver code.
	int skip = false;

	// Number of frames currently in internal sound buffer.  Set by the system emulation code, to be read by the driver code.
	int32 SoundBufSize = 0;

	// Number of cycles that this frame consumed, using MDFNGI::MasterClock as a time base.
	// Set by emulation code.
	// MasterCycles value at last MidSync(), 0 if mid sync isn't implemented for the emulation module in use.
	int64 MasterCycles = 0;
};

class CDIF;

struct RMD_Media
{
 std::string Name;
 unsigned MediaType;	// Index into RMD_Layout::MediaTypes
 std::vector<std::string> Orientations;	// The vector may be empty.
};

struct RMD_MediaType
{
 std::string Name;
};

struct RMD_State
{
 std::string Name;

 bool MediaPresent;
 bool MediaUsable;	// Usually the same as MediaPresent.
 bool MediaCanChange;
};

struct RMD_Drive
{
 std::string Name;

 std::vector<RMD_State> PossibleStates;	// Ideally, only one state will have MediaPresent == true.
 std::vector<unsigned> CompatibleMedia;	// Indexes into RMD_Layout::MediaTypes
 unsigned MediaMtoPDelay;		// Recommended minimum delay, in milliseconds, between a MediaPresent == false state and a MediaPresent == true state; to be enforced
					// by the media changing user interface.
};

struct RMD_DriveDefaults
{
 uint32 State;
 uint32 Media;
 uint32 Orientation;
};

struct RMD_Layout
{
 std::vector<RMD_Drive> Drives;
 std::vector<RMD_MediaType> MediaTypes;
 std::vector<RMD_Media> Media;
 std::vector<RMD_DriveDefaults> DrivesDefaults;
};

struct GameDB_Entry
{
 std::string GameID;
 bool GameIDIsHash = false;
 std::string Name;
 std::string Setting;
 std::string Purpose;
};

struct GameDB_Database
{
 std::string ShortName;
 std::string FullName;
 std::string Description;

 std::vector<GameDB_Entry> Entries;
};



//===========================================

typedef struct
{
 // Time base for EmulateSpecStruct::MasterCycles
 // MasterClock must be >= MDFN_MASTERCLOCK_FIXED(1.0)
 // All or part of the fractional component may be ignored in some timekeeping operations in the emulator to prevent integer overflow,
 // so it is unwise to have a fractional component when the integral component is very small(less than say, 10000).
 #define MDFN_MASTERCLOCK_FIXED(n)	((int64)((double)(n) * (1LL << 32)))
 int64 MasterClock;

 int lcm_width;
 int lcm_height;

 void *dummy_separator;	//

 int nominal_width;
 int nominal_height;

 int fb_width;		// Width of the framebuffer(not necessarily width of the image).  MDFN_Surface width should be >= this.
 int fb_height;		// Height of the framebuffer passed to the Emulate() function(not necessarily height of the image)

 uint8 MD5[16];

 RMD_Layout* RMD;

 // For mouse relative motion.
 double mouse_sensitivity;


 //
 // For absolute coordinates(IDIT_X_AXIS and IDIT_Y_AXIS), usually mapped to a mouse(hence the naming).
 //
 float mouse_scale_x, mouse_scale_y;
 float mouse_offs_x, mouse_offs_y; 
} MDFNGI;

//===========================================

int StateAction(StateMem *sm, int load, int data_only);

extern retro_log_printf_t log_cb;

#endif
