CC ?= gcc

INC := -I${ROOT} -I${ROOT}/common -I${ROOT}/decode -I${ROOT}/prf -I${ROOT}/hash -I${ROOT}/gf2x -I${ROOT}/pickyfix

# CFLAGS := -ggdb -O3 $(INC) -pg
CFLAGS := -O3 $(INC)


uname_m := $(shell uname -m)

ifeq ($(uname_m),aarch64)
  AARCH64 := 1
  USE_OPENSSL := 1
else
  ifeq ($(uname_m),x86)
    X86 := 1
    CFLAGS += -m32 -maes
  else
    ifeq ($(uname_m),x86_64)
      X86_64 := 1
      CFLAGS += -m64 -maes
    else
      $(error "Only x86_64, x86, and aarch64 platforms are currently supported.")
    endif
  endif
endif

ifdef USE_UNSAFE_CODE_FOR_EXTRAPOLATION
    CFLAGS += -DUSE_UNSAFE_CODE_FOR_EXTRAPOLATION
endif

ifdef RDTSC
    CFLAGS += -DRDTSC
endif

ifdef VERBOSE
    CFLAGS += -DVERBOSE=$(VERBOSE)
endif

ifdef TEST_BGF
    CFLAGS += -DTEST_BGF
endif

ifdef TEST_PICKYFIX
    CFLAGS += -DTEST_PICKYFIX
endif

ifdef MAX_IT
    CFLAGS += -DMAX_IT=$(MAX_IT)
endif

ifdef FIXED_SEED
    CFLAGS += -DFIXED_SEED=1
endif

ifdef USE_LARGE_SORTING_TABLE
    CFLAGS += -DUSE_LARGE_SORTING_TABLE=$(USE_LARGE_SORTING_TABLE)
endif

ifdef NUM_OF_TESTS
    CFLAGS += -DNUM_OF_TESTS=$(NUM_OF_TESTS)
endif

ifdef T1
    CFLAGS += -DT1=$(T1)
endif

ifdef R_BITS
    CFLAGS += -DR_BITS=$(R_BITS)
endif

ifndef AARCH64
    CFLAGS += -mno-red-zone 
endif
CFLAGS += -std=c99
CFLAGS += -fvisibility=hidden -Wall -Wextra -Werror -Wpedantic
# CFLAGS += -fvisibility=hidden -funsigned-char -Wall -Wextra -Wpedantic # No Werror for testing
CFLAGS += -Wunused -Wcomment -Wchar-subscripts -Wuninitialized -Wshadow
CFLAGS += -Wwrite-strings -Wno-deprecated-declarations -Wno-unknown-pragmas -Wformat-security
CFLAGS += -Wcast-qual -Wunused-result -fPIC

ifeq ($(CC),gcc)
    CFLAGS += -funroll-all-loops
endif

ifdef ASAN
    CFLAGS += -fsanitize=address -fsanitize-address-use-after-scope -fno-omit-frame-pointer
endif

ifdef TSAN
    CFLAGS += -fsanitize=thread
endif

ifdef UBSAN
    CFLAGS += -fsanitize=undefined
endif

ifndef VERBOSE
    CFLAGS += -Wcast-align
endif

#Avoiding GCC 4.8 bug
CFLAGS += -Wno-missing-braces -Wno-missing-field-initializers

ifdef AVX512
    CFLAGS += -mavx512f -mavx512bw -mavx512dq -DAVX512
    SUF = _avx512
else
    ifdef AVX2
        CFLAGS += -mavx2
        SUF = _avx2
    else
        PORTABLE = 1
        CFLAGS += -DPORTABLE
        SUF = _portable
    endif
endif

ifdef LEVEL
    CFLAGS += -DLEVEL=$(LEVEL)
endif

ifdef USE_OPENSSL
    CFLAGS += -DUSE_OPENSSL
    OPENSSL=1
endif

ifdef OPENSSL_DIR
    #Add OpenSSL_DIR
    CFLAGS += -I$(OPENSSL_DIR)/include 
    OPENSSL=1
    EXTERNAL_LIBS += -L$(OPENSSL_DIR)
endif

ifdef OPENSSL
    EXTERNAL_LIBS += -lcrypto -ldl -lpthread
endif

ifdef USE_NIST_RAND
    ifdef FIXED_SEED
        $(error cant have both FIXED_SEED and USE_NIST_RAND)
    endif

    ifndef OPENSSL_DIR
        $(error OPENSSL_DIR path variable is missing)
    endif

    #Turn on NIST_RAND
    CFLAGS += -DUSE_NIST_RAND=1
endif

CFLAGS += -fopenmp
