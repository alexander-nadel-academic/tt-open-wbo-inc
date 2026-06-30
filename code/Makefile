# VERSION    = core or simp 
# SOLVERNAME = name of the SAT solver
# SOLVERDIR  = subdirectory of the SAT solver
# NSPACE     = namespace of the SAT solver
# 
# e.g. minisat compilation with core version:
#
# VERSION    = core
# SOLVERNAME = "Minisat"
# SOLVERDIR  = minisat
# NSPACE     = Minisat
#

VERSION    = core

# Glucose4_1
#SOLVERNAME = "Glucose4_1"
#SOLVERDIR  = glucose4.1
#NSPACE     = Glucose

# IntelSATSolver
SOLVERNAME = "IntelSATSolver"
SOLVERDIR  = topor
NSPACE     = ToporWrapper
# clause buffer index type: either uint32_t or uint64_t
CLSIND = uint32_t
# compress clause buffer? (can be either false or true; expected to work well only with CLSIND = uint64_t)
COMPRESS = false

# THE REMAINING OF THE MAKEFILE SHOULD BE LEFT UNCHANGED
EXEC       = tt-open-wbo-inc-${SOLVERNAME}
ifeq ($(SOLVERDIR),topor)
	DEPDIR     = topor mtl utils core 
else
	DEPDIR     = mtl utils core 
endif

DEPDIR     +=  ../../encodings ../../algorithms ../../graph ../../classifier ../../clusterings .
MROOT      = $(PWD)/solvers/$(SOLVERDIR)
LFLAGS     += -lgmpxx -lgmp
CFLAGS     = -O3 -Wall -Wno-parentheses -Wno-class-memaccess -Wno-misleading-indentation -std=c++20 -DNSPACE=$(NSPACE) -DSOLVERNAME=$(SOLVERNAME) -DVERSION=$(VERSION) -DCLSIND=$(CLSIND) -DCOMPRESS=$(COMPRESS)
UNAME_S   := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    LFLAGS += -L/opt/homebrew/lib
    CFLAGS += -I/opt/homebrew/include
    # Auto-detect highest-versioned Homebrew g++ and gcc
    BREW_GXX := $(shell ls /opt/homebrew/bin/g++-* 2>/dev/null | grep -E 'g\+\+-[0-9]+$$' | sort -t- -k2 -n | tail -1)
    BREW_GCC := $(shell ls /opt/homebrew/bin/gcc-* 2>/dev/null | grep -E 'gcc-[0-9]+$$' | sort -t- -k2 -n | tail -1)
    ifneq ($(BREW_GXX),)
        CXX := $(BREW_GXX)
    endif
    ifneq ($(BREW_GCC),)
        CC := $(BREW_GCC)
    endif
endif
#CFLAGS     = -g -Wall -Wno-parentheses -std=c++20 -DNSPACE=$(NSPACE) -DSOLVERNAME=$(SOLVERNAME) -DVERSION=$(VERSION)
ifeq ($(SOLVERDIR),glucose4.1)
    CFLAGS += -Wno-sign-compare -Wno-reorder -Wno-unused-value
endif
ifeq ($(VERSION),simp)
DEPDIR     += simp
CFLAGS     += -DSIMP=1 
ifeq ($(SOLVERDIR),glucored)
LFLAGS     += -pthread
CFLAGS     += -DGLUCORED
DEPDIR     += reducer glucored
endif
endif
include $(MROOT)/mtl/template.mk

# Suppress warnings in third-party solver internals only
SOLVER_NOWARN = -Wno-strict-aliasing -Wno-class-memaccess -Wno-misleading-indentation
$(MROOT)/topor/%.o $(MROOT)/topor/%.op $(MROOT)/topor/%.od $(MROOT)/topor/%.or: CFLAGS += $(SOLVER_NOWARN)
$(MROOT)/core/%.o $(MROOT)/core/%.op $(MROOT)/core/%.od $(MROOT)/core/%.or:   CFLAGS += $(SOLVER_NOWARN)
$(MROOT)/utils/%.o $(MROOT)/utils/%.op $(MROOT)/utils/%.od $(MROOT)/utils/%.or: CFLAGS += $(SOLVER_NOWARN)
$(MROOT)/mtl/%.o $(MROOT)/mtl/%.op $(MROOT)/mtl/%.od $(MROOT)/mtl/%.or:     CFLAGS += $(SOLVER_NOWARN)
