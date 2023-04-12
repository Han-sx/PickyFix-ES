include ../inc.mk

CSRC = aes_ctr_prf.c sampling.c

ifdef PORTABLE
    CSRC += sampling_portable.c
else
    SSRC += sampling${SUF}.S
endif

ifndef USE_OPENSSL
    CSRC += aes.c 
    SSRC += vaes256_key_expansion.S
endif

include ../rules.mk

