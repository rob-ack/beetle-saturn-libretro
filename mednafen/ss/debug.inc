/******************************************************************************/
/* Mednafen Sega Saturn Emulation Module                                      */
/******************************************************************************/
/* debug.inc:
**  Copyright (C) 2015-2019 Mednafen Team
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

 template<unsigned which>
 static void SS_DBG_Wrap(const char* format, ...) noexcept
 {
 }

 static INLINE void DBG_AddBranchTrace(unsigned which, uint32 to, int exception, unsigned vecnum = 0) { }

template<unsigned which>
static MDFN_COLD INLINE void DBG_CPUHandler(void) { }

static INLINE bool DBG_NeedCPUHooks(void) { return false; }
static INLINE void DBG_SetEffTS(const sscpu_timestamp_t eff_ts) { }
static INLINE bool DBG_InSlaveStep(void) { return false; }
