#ifndef __DISC_H__
#define __DISC_H__

#include <libretro.h>
#include "mednafen/git.h"
#include "mednafen/mednafen-types.h"

// These routines handle disc drive front-end.

void disc_init( retro_environment_t environ_cb );

void disc_cleanup(void);

bool DetectRegion( unsigned* region );

bool DiscSanityChecks(void);

void disc_select( unsigned disc_num );

bool disc_load_content( MDFNGI* game_inteface, const char *name, uint8* fd_id, char* sgid, char *sgname, char *sgarea, bool image_memcache );

#endif
