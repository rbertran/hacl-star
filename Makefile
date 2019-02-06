# This Makefile covers all of the present repository (HACL* + Vale + EverCrypt)
# with the exclusion of legacy code found in secure_api, code/old and specs/old.
#
# From a high-level perspective, the coarse-grained dependency graph is:
#
#            merkle_tree
#                |
#             evercrypt                secure_api
#               /  \                      |
#           code   vale                code/old
#           /   \  /                      |
#         lib   specs                  specs/old
#


##########################
# Top-level entry points #
##########################

# TODO: compile-merkle-tree, compile-evercrypt + variants
all: compile-compact compile-generic compile-compact-msvc # secure_api.old

# Any file in code/tests is taken to contain a `main` function.
# Any file in specs/tests is taken to contain a `test` function.
# TODO: test-merkle-tree, test-evercrypt
test: test-c test-ml
test-c: $(subst .,_,$(patsubst %.fst,test-c-%,$(notdir $(wildcard code/tests/*.fst))))
test-ml: $(subst .,_,$(patsubst %.fst,test-ml-%,$(notdir $(wildcard specs/tests/*.fst))))

ci: all test

# Backwards-compat target
.PHONY: secure_api.old
secure_api.old:
	$(MAKE) -C secure_api


#################
# Configuration #
#################

IMPORT_FSTAR_TYPES = $(VALE_HOME)/bin/importFStarTypes.exe
PYTHON3 = $(shell tools/findpython3.sh)
ifeq ($(OS),Windows_NT)
  MONO =
else
  MONO = mono
endif


####################################################
# Dependency graphs for Vale, then F* source files #
####################################################

# The set of .vaf files we want to translate to F*.
VALE_ROOTS = $(filter-out %.types.vaf,$(wildcard $(addsuffix /*.vaf,$(VALE_DIRS))))

# F* files stemming from Vale files
VALE_FSTS = $(patsubst %.vaf,%.fst,$(VALE_ROOTS))

# The complete set of F* files -- only meaningful in the second stage of this build.
FSTAR_ROOTS = $(wildcard $(addsuffix /*.fsti,$(DIRS)) $(addsuffix /*.fst,$(DIRS)))

include Makefile.common

# We currently force regeneration of three depend files... this is... long...
ifndef MAKE_RESTARTS
.fstar-depend-%: .FORCE
	@$(FSTAR_NO_FLAGS) --dep $* $(FSTAR_ROOTS) --extract '* -Prims -LowStar -Lib.Buffer -Hacl -FStar +FStar.Endianness +FStar.Kremlin.Endianness' > $@

.vale-depend: .fstar-depend-make .FORCE
	@$(PYTHON3) tools/valedepend.py \
	  $(addprefix -include ,$(INCLUDES)) \
	  $(addprefix -in ,$(VALE_ROOTS)) \
	  -dep $< \
	  > $@

.PHONY: .FORCE
.FORCE:
endif

include .fstar-depend-full
include .vale-depend


###################################################
# First stage: producing F* files from Vale files #
###################################################

%.dump: %.checked
	$(FSTAR) --dump_module $(subst prims,Prims,$(basename $(notdir $*))) \
          --print_implicits --print_universes --print_effect_args --print_full_names \
	  --print_bound_var_types --ugly --admit_smt_queries true \
	  $* > $@

%.types.vaf:
	$(MONO) $(IMPORT_FSTAR_TYPES) $(addprefix -in ,$^) -out $@

# Always pass operator.vaf as an -include to Vale, except for the file itself.
VALE_FLAGS = -include $(HACL_HOME)/vale/code/lib/util/operator.vaf

$(HACL_HOME)/vale/code/lib/util/operator.fst: VALE_FLAGS=

%.fsti:
	@if ! [ "$*.vaf" == "$<" ]; then echo "Makefile bug: trying to produce an .fst without a .vaf"; false; fi
	$(MONO) $(VALE_HOME)/bin/vale.exe -fstarText -quickMods \
	  -typecheck -include $*.types.vaf \
	  $(VALE_FLAGS) \
	  -in $< -out $@ -outi $@i

# Force linearization of the rule above
%.fst: %.fsti

# A pseudo-target for the first stage.
vaf-to-fst: $(VALE_FSTS)


####################################
# Second stage: verifying F* files #
####################################

$(HACL_HOME)/vale/%.checked: FSTAR_FLAGS=--z3cliopt smt.arith.nl=false \
  --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 \
  --smtencoding.elim_box true --smtencoding.l_arith_repr native \
  --smtencoding.nl_arith_repr wrapped

%.checked:
	$(FSTAR) $(FSTAR_FLAGS) $< && \
	touch $@

# 3. Extraction. Note that all the C files are prefixed with Hacl_. Cleaner!

.PRECIOUS: %.krml

$(OUTPUT_DIR)/%.krml:
	$(FSTAR) --codegen Kremlin \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

COMPACT_FLAGS=-bundle Hacl.Hash.MD5+Hacl.Hash.Core.MD5+Hacl.Hash.SHA1+Hacl.Hash.Core.SHA1+Hacl.Hash.SHA2+Hacl.Hash.Core.SHA2+Hacl.Hash.Core.SHA2.Constants=Hacl.Hash.*[rename=Hacl_Hash] \
  -bundle Hacl.Impl.SHA3+Hacl.SHA3=[rename=Hacl_SHA3] \
  -bundle Prims \
  -bundle LowStar.* \
  -bundle C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] \
  -bundle 'Test.*,WindowsHack' \
  -minimal \
  -add-include '"kremlin/internal/types.h"' \
  -add-include '"kremlin/internal/target.h"' \
  -add-include '"kremlin/c_endianness.h"' \
  -add-include '<string.h>' \
  -fno-shadow -fcurly-braces

HAND_WRITTEN_C	= Lib.PrintBuffer Lib.RandomBuffer
HAND_WRITTEN_FILES = $(wildcard $(LIB_DIR)/c/*.c)
DEFAULT_FLAGS	= $(addprefix -library ,$(HAND_WRITTEN_C)) \
  -bundle Lib.*[rename=Hacl_Lib] -bundle Hacl.Test.*

# For the time being, we rely on the old extraction to give us self-contained
# files

.PHONY: old-%
old-%:
	$(MAKE) -C code/old -f Makefile.old $*

HACL_OLD_FILES=\
  code/old/experimental/aesgcm/aesgcm-c/Hacl_AES.c \
  code/old/curve25519/x25519-c/Hacl_Curve25519.c \
  code/old/ed25519/ed25519-c/Hacl_Ed25519.c \
  code/old/salsa-family/chacha-c/Hacl_Chacha20.c \
  code/old/poly1305/poly-c/AEAD_Poly1305_64.c \
  code/old/poly1305/poly-c/Hacl_Poly1305_64.c \
  code/old/api/aead-c/Hacl_Chacha20Poly1305.c

dist/compact/Makefile.basic: EXTRA=$(COMPACT_FLAGS)

dist/compact-msvc/Makefile.basic: EXTRA=$(COMPACT_FLAGS) -falloca -ftail-calls

dist/compact-c89/Makefile.basic: EXTRA=$(COMPACT_FLAGS) -fc89 -ccopt -std=c89
dist/compact-c89/Makefile.basic: HACL_OLD_FILES:=$(subst -c,-c89,$(HACL_OLD_FILES))

.PRECIOUS: dist/%/Makefile.basic
dist/%/Makefile.basic: $(ALL_KRML_FILES) dist/headers/Makefile.basic $(HAND_WRITTEN_FILES) | old-extract-c
	mkdir -p $(dir $@)
	cp $(HACL_OLD_FILES) $(patsubst %.c,%.h,$(HACL_OLD_FILES)) $(dir $@)
	cp $(HAND_WRITTEN_FILES) dist/headers/*.h $(dir $@)
	$(KRML) $(DEFAULT_FLAGS) $(EXTRA) \
	  -tmpdir $(dir $@) -skip-compilation \
	  -bundle Spec.*[rename=Hacl_Spec] $(filter %.krml,$^) \
	  -ccopt -Wno-unused \
	  -warn-error @4 \
	  -fparentheses \
	  $(notdir $(HACL_OLD_FILES)) \
	  $(notdir $(HAND_WRITTEN_FILES)) \
	  -o libhacl.a

# Auto-generates headers for the hand-written C files. If a signature changes on
# the F* side, hopefully this will ensure the C file breaks. Note that there's
# no conflict between the headers because this generates
# Lib_Foobar while the run above generates a single Hacl_Lib.
dist/headers/Makefile.basic: $(ALL_KRML_FILES)
	$(KRML) \
	  -tmpdir $(dir $@) -skip-compilation \
	  $(patsubst %,-bundle %=,$(HAND_WRITTEN_C)) \
	  $(patsubst %,-library %,$(HAND_WRITTEN_C)) \
	  -minimal -add-include '"kremlib.h"' \
	  -bundle '\*,WindowsBug' $^

# Auto-generates a single C test file.
.PRECIOUS: dist/test/c/%.c
dist/test/c/%.c: $(ALL_KRML_FILES)
	$(KRML) \
	  -tmpdir $(dir $@) -skip-compilation \
	  -no-prefix $(subst _,.,$*) \
	  -library Hacl,Lib \
	  -fparentheses -fcurly-braces -fno-shadow \
	  -minimal -add-include '"kremlib.h"' \
	  -bundle '*[rename=$*]' $^

# 4. Compilation (recursive make invocation relying on KreMLin-generated Makefile)

compile-%: dist/%/Makefile.basic
	$(MAKE) -C $(dir $<) -f $(notdir $<)

# 5. C tests

.PRECIOUS: dist/test/c/%.exe
dist/test/c/%.exe: dist/test/c/%.c compile-generic
	# Linking with full kremlib since tests may use TestLib, etc.
	$(CC) -Wall -Wextra -Werror -Wno-unused-parameter $< -o $@ dist/generic/libhacl.a \
	  -I $(dir $@) -I $(KREMLIN_HOME)/include \
	  $(KREMLIN_HOME)/kremlib/dist/generic/libkremlib.a

test-c-%: dist/test/c/%.exe
	$<

# 5. OCaml tests, for specs

include $(FSTAR_HOME)/ulib/ml/Makefile.include

TAC = $(shell which tac >/dev/null 2>&1 && echo "tac" || echo "tail -r")

ALL_CMX_FILES = $(patsubst %.ml,%.cmx,$(shell echo $(ALL_ML_FILES) | $(TAC)))

OCAMLOPT += -I $(OUTPUT_DIR)

%.cmx: %.ml
	$(OCAMLOPT) -c $< -o $@

$(OUTPUT_DIR)/%.ml:
	$(FSTAR) $(subst .checked,,$<) --codegen OCaml --extract_module $(subst .fst.checked,,$(notdir $<))

.PRECIOUS: dist/test/ml/%_AutoTest.ml
dist/test/ml/%_AutoTest.ml:
	mkdir -p $(dir $@)
	echo "if not ($*.test ()) then (print_endline \"$* failed\"; exit 1)" > $@

# Relying on the --extract argument of fstar --dep to have a reasonable
# over-approximation.
dist/test/ml/%.exe: $(ALL_CMX_FILES) dist/test/ml/%_AutoTest.ml
	$(OCAMLOPT) $^ -o $@

test-ml-%: dist/test/ml/%.exe
	$<
