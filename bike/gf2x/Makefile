include ../inc.mk

CSRC = gf2x_mul.c

ifdef PORTABLE
    CSRC += gf2x_portable.c
else
    SSRC = gf_mul.S red.S
endif

ifdef USE_OPENSSL
  CSRC += openssl_utils.c
endif

include ../rules.mk