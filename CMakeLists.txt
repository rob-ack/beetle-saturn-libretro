project(mednafen_saturn_libretro)

cmake_minimum_required(VERSION 3.20)

set(CMAKE_CXX_STANDARD 23)

set(CORE_DIR ./)
add_compile_definitions(WANT_SS_EMU)

set(NEED_CD ON)
set(HAVE_CHD ON)

set(NEED_CD ON)
set(NEED_TREMOR ON)
set(NEED_BPP 32)
set(NEED_DEINTERLACER ON)
set(NEED_THREADING ON)

add_compile_definitions(NOMINMAX)

######################################

#SOURCES_CXX :=
#SOURCES_C   :=
#
#DEPS_DIR     := $(CORE_DIR)/deps
set(DEPS_DIR deps)
#LIBRETRO_COMM_DIR := $(CORE_DIR)/libretro-common
set(LIBRETRO_COMM_DIR libretro-common)
#MEDNAFEN_DIR := $(CORE_DIR)/mednafen
set(MEDNAFEN_DIR mednafen)
#CORE_EMU_DIR := $(MEDNAFEN_DIR)/ss
set(CORE_EMU_DIR ${MEDNAFEN_DIR}/ss)
#CDROM_DIR    := $(MEDNAFEN_DIR)/cdrom
set(CDROM_DIR ${MEDNAFEN_DIR}/cdrom)
#
#ZLIB_INCFLAGS := -I$(DEPS_DIR)/zlib
include_directories(${DEPS_DIR}/zlib)
#INCFLAGS := -I$(CORE_DIR) -I$(MEDNAFEN_DIR) -I$(MEDNAFEN_DIR)/include -I$(MEDNAFEN_DIR)/intl -I$(MEDNAFEN_DIR)/hw_sound -I$(MEDNAFEN_DIR)/hw_cpu -I$(MEDNAFEN_DIR)/hw_misc -I$(LIBRETRO_COMM_DIR)/include 
include_directories(
    ./ 
    ${MEDNAFEN_DIR} 
    ${MEDNAFEN_DIR}/include 
    ${MEDNAFEN_DIR}/intl 
    ${MEDNAFEN_DIR}/hw_sound 
    ${MEDNAFEN_DIR}/hw_cpu 
    ${MEDNAFEN_DIR}/hw_misc 
    ${LIBRETRO_COMM_DIR}/include 
)

set(HEADERS ${HEADERS}
    ${DEPS_DIR}/zlib
    ./ 
    ${MEDNAFEN_DIR} 
    ${MEDNAFEN_DIR}/hw_cpu 
    ${LIBRETRO_COMM_DIR}/include 
)

#
#
#ZLIB_SOURCES_C := $(DEPS_DIR)/zlib/adler32.c \
#	     $(DEPS_DIR)/zlib/crc32.c \
#	     $(DEPS_DIR)/zlib/inffast.c \
#	     $(DEPS_DIR)/zlib/inflate.c \
#	     $(DEPS_DIR)/zlib/inftrees.c
set(ZLIB_SOURCES_C 
        ${DEPS_DIR}/zlib/adler32.c
	    ${DEPS_DIR}/zlib/crc32.c
	    ${DEPS_DIR}/zlib/inffast.c
	    ${DEPS_DIR}/zlib/inflate.c
	    ${DEPS_DIR}/zlib/inftrees.c
)

#
#ifeq ($(NEED_THREADING), 1)
#   FLAGS += -DWANT_THREADING -DHAVE_THREADS
add_compile_definitions(WANT_THREADING HAVE_THREADS)
#endif
#
#ifeq ($(NEED_DEINTERLACER), 1)
#   FLAGS += -DNEED_DEINTERLACER
add_compile_definitions(NEED_DEINTERLACER)
#endif
#
#ifeq ($(NEED_BPP), 8)
#FLAGS += -DWANT_8BPP
#endif
#
#ifeq ($(NEED_BPP), 16)
#FLAGS += -DWANT_16BPP
#endif
#
#ifeq ($(NEED_BPP), 32)
#FLAGS += -DWANT_32BPP
add_compile_definitions(WANT_32BPP)
#endif
#
#ifeq ($(WANT_NEW_API), 1)
#FLAGS += -DWANT_NEW_API
add_compile_definitions(WANT_NEW_API)
#endif
#
#ifeq ($(NO_COMPUTED_GOTO), 1)
#FLAGS += -DNO_COMPUTED_GOTO
#endif
#
#ifeq ($(FRONTEND_SUPPORTS_RGB565), 1)
#FLAGS += -DFRONTEND_SUPPORTS_RGB565
add_compile_definitions(FRONTEND_SUPPORTS_RGB565)
#endif
#
#ifeq ($(NEED_CD), 1)
if(${NEED_CD})
#   FLAGS += -DNEED_CD
    add_compile_definitions(NEED_CD)
#endif
endif(${NEED_CD})
#
#ifeq ($(HAVE_CHD), 1)
if(${HAVE_CHD})
#   FLAGS += -DHAVE_CHD -D_7ZIP_ST
add_compile_definitions(HAVE_CHD _7ZIP_ST)
#ifeq ($(SYSTEM_LIBCHDR), 1)
#   INCFLAGS += $(shell pkg-config --cflags libchdr)
#   LIBS += $(shell pkg-config --libs libchdr)
#else
#   INCFLAGS += -I$(DEPS_DIR)/crypto \
#	       -I$(DEPS_DIR)/lzma/C \
#	       -I$(DEPS_DIR)/libchdr \
#	       -I$(DEPS_DIR)/libchdr/include \
#	       -I$(DEPS_DIR)/libchdr/include/libchdr
include_directories(
    ${DEPS_DIR}/crypto
    ${DEPS_DIR}/lzma/C 
    ${DEPS_DIR}/libchdr 
    ${DEPS_DIR}/libchdr/include 
    ${DEPS_DIR}/libchdr/include/libchdr    
)
set(HEADERS ${HEADERS}
    ${DEPS_DIR}/crypto
    ${DEPS_DIR}/libchdr 
    ${DEPS_DIR}/libchdr/include 
    ${DEPS_DIR}/libchdr/include/libchdr   
)

#endif
#endif
endif(${HAVE_CHD})
#
#ifeq ($(NEED_TREMOR), 1)
#   FLAGS += -DNEED_TREMOR
add_compile_definitions(NEED_TREMOR)
#endif
#
#SOURCES_CXX += \
#	$(CORE_EMU_DIR)/db.cpp \
#	$(CORE_EMU_DIR)/cdb.cpp \
#	$(CORE_EMU_DIR)/sound.cpp \
#	$(CORE_EMU_DIR)/cart.cpp \
#	$(CORE_EMU_DIR)/ss.cpp \
#	$(CORE_EMU_DIR)/scu_dsp_gen.cpp \
#	$(CORE_EMU_DIR)/scu_dsp_mvi.cpp \
#	$(CORE_EMU_DIR)/scu_dsp_jmp.cpp \
#	$(CORE_EMU_DIR)/scu_dsp_misc.cpp \
#	$(CORE_EMU_DIR)/vdp1.cpp \
#	$(CORE_EMU_DIR)/vdp1_line.cpp \
#	$(CORE_EMU_DIR)/vdp1_sprite.cpp \
#	$(CORE_EMU_DIR)/vdp1_poly.cpp \
#	$(CORE_EMU_DIR)/vdp2.cpp \
#	$(CORE_EMU_DIR)/vdp2_render.cpp \
#	$(CORE_EMU_DIR)/smpc.cpp \
#	$(CORE_EMU_DIR)/input/gamepad.cpp \
#	$(CORE_EMU_DIR)/input/gun.cpp \
#	$(CORE_EMU_DIR)/input/3dpad.cpp \
#	$(CORE_EMU_DIR)/input/mouse.cpp \
#	$(CORE_EMU_DIR)/input/multitap.cpp \
#	$(CORE_EMU_DIR)/input/mission.cpp \
#	$(CORE_EMU_DIR)/input/keyboard.cpp \
#	$(CORE_EMU_DIR)/input/jpkeyboard.cpp \
#	$(CORE_EMU_DIR)/input/wheel.cpp
set(SOURCES_CXX ${SOURCES_CXX} 
    ${CORE_EMU_DIR}/db.cpp 
    ${CORE_EMU_DIR}/cdb.cpp 
    ${CORE_EMU_DIR}/sound.cpp 
    ${CORE_EMU_DIR}/cart.cpp 
    ${CORE_EMU_DIR}/ss.cpp 
    ${CORE_EMU_DIR}/scu_dsp_gen.cpp 
    ${CORE_EMU_DIR}/scu_dsp_mvi.cpp 
    ${CORE_EMU_DIR}/scu_dsp_jmp.cpp 
    ${CORE_EMU_DIR}/scu_dsp_misc.cpp 
    ${CORE_EMU_DIR}/vdp1.cpp 
    ${CORE_EMU_DIR}/vdp1_line.cpp 
    ${CORE_EMU_DIR}/vdp1_sprite.cpp 
    ${CORE_EMU_DIR}/vdp1_poly.cpp 
    ${CORE_EMU_DIR}/vdp2.cpp 
    ${CORE_EMU_DIR}/vdp2_render.cpp 
    ${CORE_EMU_DIR}/smpc.cpp 
    ${CORE_EMU_DIR}/input/gamepad.cpp 
    ${CORE_EMU_DIR}/input/gun.cpp 
    ${CORE_EMU_DIR}/input/3dpad.cpp 
    ${CORE_EMU_DIR}/input/mouse.cpp 
    ${CORE_EMU_DIR}/input/multitap.cpp 
    ${CORE_EMU_DIR}/input/mission.cpp 
    ${CORE_EMU_DIR}/input/keyboard.cpp 
    ${CORE_EMU_DIR}/input/jpkeyboard.cpp 
    ${CORE_EMU_DIR}/input/wheel.cpp
)
#
#SOURCES_CXX += \
#	       $(CORE_EMU_DIR)/cart/backup.cpp \
#	       $(CORE_EMU_DIR)/cart/cs1ram.cpp \
#	       $(CORE_EMU_DIR)/cart/debug.cpp \
#	       $(CORE_EMU_DIR)/cart/extram.cpp \
#	       $(CORE_EMU_DIR)/cart/rom.cpp \
#	       $(CORE_EMU_DIR)/cart/ar4mp.cpp
set(SOURCES_CXX ${SOURCES_CXX} 
    ${CORE_EMU_DIR}/cart/backup.cpp 
    ${CORE_EMU_DIR}/cart/cs1ram.cpp 
    ${CORE_EMU_DIR}/cart/debug.cpp 
    ${CORE_EMU_DIR}/cart/extram.cpp 
    ${CORE_EMU_DIR}/cart/rom.cpp 
    ${CORE_EMU_DIR}/cart/ar4mp.cpp
)
#
#SOURCES_CXX += $(MEDNAFEN_DIR)/hw_cpu/m68k/m68k.cpp
set(SOURCES_CXX ${SOURCES_CXX} 
    ${MEDNAFEN_DIR}/hw_cpu/m68k/m68k.cpp
)

#
#SOURCES_C += $(CORE_DIR)/libretro_cbs.c
set(SOURCES_C ${SOURCES_C} 
    ${CORE_DIR}/libretro_cbs.c
)
#
#ifeq ($(NEED_TREMOR), 1)
#   SOURCES_C += $(wildcard $(MEDNAFEN_DIR)/tremor/*.c)
FILE(GLOB MEDNAFEN_DIR_tremor ${MEDNAFEN_DIR}/tremor/*.c)
set(SOURCES_C ${SOURCES_C} 
    ${MEDNAFEN_DIR_tremor}
)
#endif
#
#SOURCES_CXX += $(CDROM_DIR)/CDAccess.cpp \
#	$(CDROM_DIR)/CDAccess_Image.cpp \
#	$(CDROM_DIR)/CDAccess_CCD.cpp \
#	$(CDROM_DIR)/CDAFReader.cpp \
#	$(CDROM_DIR)/CDAFReader_Vorbis.cpp \
#	$(CDROM_DIR)/cdromif.cpp \
#	$(CDROM_DIR)/CDUtility.cpp \
#	$(CDROM_DIR)/lec.cpp \
#	$(CDROM_DIR)/galois.cpp \
#	$(CDROM_DIR)/recover-raw.cpp \
#	$(CDROM_DIR)/l-ec.cpp \
#	$(CDROM_DIR)/edc_crc32.cpp
set(SOURCES_CXX ${SOURCES_CXX} 
    ${CDROM_DIR}/CDAccess.cpp
    ${CDROM_DIR}/CDAccess_Image.cpp
    ${CDROM_DIR}/CDAccess_CCD.cpp 
    ${CDROM_DIR}/CDAFReader.cpp 
    ${CDROM_DIR}/CDAFReader_Vorbis.cpp 
    ${CDROM_DIR}/cdromif.cpp 
    ${CDROM_DIR}/CDUtility.cpp 
    ${CDROM_DIR}/lec.cpp 
    ${CDROM_DIR}/galois.cpp 
    ${CDROM_DIR}/recover-raw.cpp 
    ${CDROM_DIR}/l-ec.cpp 
    ${CDROM_DIR}/edc_crc32.cpp
)
#FLAGS += -DNEED_CD
add_compile_definitions(NEED_CD)
#
#ifeq ($(HAVE_CHD), 1)
#ifneq ($(SYSTEM_LIBCHDR), 1)
#LZMA_DIR := $(DEPS_DIR)/lzma/src
set(LZMA_DIR ${DEPS_DIR}/lzma/src)
#LIBCHDR_DIR := $(DEPS_DIR)/libchdr/src
set(LIBCHDR_DIR ${DEPS_DIR}/libchdr/src)
#INCFLAGS += -I$(DEPS_DIR)/lzma/include
include_directories(${DEPS_DIR}/lzma/include)
#SOURCES_C += \
#	$(DEPS_DIR)/crypto/md5.c \
#	$(DEPS_DIR)/crypto/sha1.c \
#	$(LZMA_DIR)/Alloc.c \
#	$(LZMA_DIR)/Bra86.c \
#	$(LZMA_DIR)/BraIA64.c \
#	$(LZMA_DIR)/CpuArch.c \
#	$(LZMA_DIR)/Delta.c \
#	$(LZMA_DIR)/LzFind.c \
#	$(LZMA_DIR)/Lzma86Dec.c \
#	$(LZMA_DIR)/LzmaDec.c \
#	$(LZMA_DIR)/LzmaEnc.c \
#	$(LIBCHDR_DIR)/libchdr_bitstream.c \
#	$(LIBCHDR_DIR)/libchdr_cdrom.c \
#	$(LIBCHDR_DIR)/libchdr_chd.c \
#	$(LIBCHDR_DIR)/libchdr_flac.c \
#	$(LIBCHDR_DIR)/libchdr_huffman.c 
set(SOURCES_C ${SOURCES_C} 
    ${DEPS_DIR}/crypto/md5.c 
    ${DEPS_DIR}/crypto/sha1.c 
    ${LZMA_DIR}/Alloc.c 
    ${LZMA_DIR}/Bra86.c 
    ${LZMA_DIR}/BraIA64.c 
    ${LZMA_DIR}/CpuArch.c 
    ${LZMA_DIR}/Delta.c 
    ${LZMA_DIR}/LzFind.c 
    ${LZMA_DIR}/Lzma86Dec.c 
    ${LZMA_DIR}/LzmaDec.c 
    ${LZMA_DIR}/LzmaEnc.c 
    ${LIBCHDR_DIR}/libchdr_bitstream.c 
    ${LIBCHDR_DIR}/libchdr_cdrom.c 
    ${LIBCHDR_DIR}/libchdr_chd.c 
    ${LIBCHDR_DIR}/libchdr_flac.c 
    ${LIBCHDR_DIR}/libchdr_huffman.c 
)
#endif
#
#SOURCES_CXX += $(CDROM_DIR)/CDAccess_CHD.cpp
set(SOURCES_CXX ${SOURCES_CXX} 
        ${CDROM_DIR}/CDAccess_CHD.cpp
)
#endif
#
#SOURCES_CXX += \
#	$(MEDNAFEN_DIR)/error.cpp \
#	$(MEDNAFEN_DIR)/settings.cpp \
#	$(MEDNAFEN_DIR)/general.cpp \
#	$(MEDNAFEN_DIR)/FileStream.cpp \
#	$(MEDNAFEN_DIR)/MemoryStream.cpp \
#	$(MEDNAFEN_DIR)/Stream.cpp \
#	$(MEDNAFEN_DIR)/state.cpp \
#	$(MEDNAFEN_DIR)/mempatcher.cpp \
#	$(MEDNAFEN_DIR)/video/Deinterlacer.cpp \
#	$(MEDNAFEN_DIR)/video/surface.cpp \
#	$(MEDNAFEN_DIR)/git.cpp \
#	$(CORE_DIR)/disc.cpp \
#	$(CORE_DIR)/input.cpp \
#	$(CORE_DIR)/libretro.cpp \
#	$(CORE_DIR)/libretro_settings.cpp
#
set(SOURCES_CXX ${SOURCES_CXX} 
	${MEDNAFEN_DIR}/error.cpp 
	${MEDNAFEN_DIR}/settings.cpp 
	${MEDNAFEN_DIR}/general.cpp 
	${MEDNAFEN_DIR}/FileStream.cpp 
	${MEDNAFEN_DIR}/MemoryStream.cpp 
	${MEDNAFEN_DIR}/Stream.cpp 
	${MEDNAFEN_DIR}/state.cpp 
	${MEDNAFEN_DIR}/mempatcher.cpp 
	${MEDNAFEN_DIR}/video/Deinterlacer.cpp 
	${MEDNAFEN_DIR}/video/surface.cpp 
	${MEDNAFEN_DIR}/git.cpp 
	${CORE_DIR}/disc.cpp 
	${CORE_DIR}/input.cpp 
	${CORE_DIR}/libretro.cpp 
	${CORE_DIR}/libretro_settings.cpp
)

#SOURCES_C += $(MEDNAFEN_DIR)/mednafen-endian.c
set(SOURCES_C ${SOURCES_C} 
    ${MEDNAFEN_DIR}/mednafen-endian.c
)
#
#SOURCES_CXX += \
#		$(MEDNAFEN_DIR)/hash/sha256.cpp \
#		$(MEDNAFEN_DIR)/hash/md5.cpp
set(SOURCES_CXX ${SOURCES_CXX} 
        ${MEDNAFEN_DIR}/hash/sha256.cpp
		${MEDNAFEN_DIR}/hash/md5.cpp
)
#
#ifeq ($(HAVE_CHD), 1)
#ifneq ($(SYSTEM_LIBCHDR), 1)
#ifeq ($(SYSTEM_ZLIB), 1)
#	INCFLAGS += $(shell pkg-config --cflags zlib)
#	LIBS += $(shell pkg-config --libs zlib)
#else
#	INCFLAGS += $(ZLIB_INCFLAGS)
#	SOURCES_C += $(ZLIB_SOURCES_C)
set(SOURCES_C ${SOURCES_C} ${ZLIB_SOURCES_C} )
#endif
#endif
#endif
#
#ifneq ($(STATIC_LINKING), 1)
#SOURCES_C += 	 $(LIBRETRO_COMM_DIR)/streams/file_stream.c \
#		 $(LIBRETRO_COMM_DIR)/file/file_path.c \
#		 $(LIBRETRO_COMM_DIR)/file/retro_dirent.c \
#		 $(LIBRETRO_COMM_DIR)/lists/dir_list.c \
#		 $(LIBRETRO_COMM_DIR)/lists/string_list.c \
#		 $(LIBRETRO_COMM_DIR)/vfs/vfs_implementation.c \
#		 $(LIBRETRO_COMM_DIR)/compat/compat_posix_string.c \
#		 $(LIBRETRO_COMM_DIR)/compat/compat_strl.c \
#		 $(LIBRETRO_COMM_DIR)/compat/compat_strcasestr.c \
#		 $(LIBRETRO_COMM_DIR)/compat/fopen_utf8.c \
#		 $(LIBRETRO_COMM_DIR)/encodings/encoding_utf.c \
#		 $(LIBRETRO_COMM_DIR)/memmap/memalign.c \
#		 $(LIBRETRO_COMM_DIR)/string/stdstring.c \
#		 $(LIBRETRO_COMM_DIR)/time/rtime.c
set(SOURCES_C ${SOURCES_C} 
    ${LIBRETRO_COMM_DIR}/streams/file_stream.c
    ${LIBRETRO_COMM_DIR}/file/file_path.c 
    ${LIBRETRO_COMM_DIR}/file/retro_dirent.c 
    ${LIBRETRO_COMM_DIR}/lists/dir_list.c 
    ${LIBRETRO_COMM_DIR}/lists/string_list.c 
    ${LIBRETRO_COMM_DIR}/vfs/vfs_implementation.c 
    ${LIBRETRO_COMM_DIR}/compat/compat_posix_string.c 
    ${LIBRETRO_COMM_DIR}/compat/compat_strl.c 
    ${LIBRETRO_COMM_DIR}/compat/compat_strcasestr.c 
    ${LIBRETRO_COMM_DIR}/compat/fopen_utf8.c 
    ${LIBRETRO_COMM_DIR}/encodings/encoding_utf.c 
    ${LIBRETRO_COMM_DIR}/memmap/memalign.c 
    ${LIBRETRO_COMM_DIR}/string/stdstring.c 
    ${LIBRETRO_COMM_DIR}/time/rtime.c
)
#
#ifeq ($(NEED_THREADING), 1)
#SOURCES_C += $(LIBRETRO_COMM_DIR)/rthreads/rthreads.c
set(SOURCES_C ${SOURCES_C} 
    ${LIBRETRO_COMM_DIR}/rthreads/rthreads.c
)
#endif
#
#endif
#

add_compile_definitions(NEED_THREADING=1 HAVE_CHD=1)
add_library(mednafen_saturn SHARED ${SOURCES_C} ${SOURCES_CXX})

###############################################

if(MSVC)
    add_definitions(/MP)
endif(MSVC)

