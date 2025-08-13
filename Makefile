OCAMLC := ocamlopt
SCHEME_IMPL := chez

SCHEME_COMMAND_chicken := csi compat_chicken.scm prelude.scm -script
SCHEME_COMMAND_chez    := scheme --script compat_chez.scm
SCHEME_COMMAND_guile   := guile -l compat_guile.scm -l prelude.scm

SCHEME_COMMAND    := $(SCHEME_COMMAND_$(SCHEME_IMPL))
SCHEME_COMPAT_LIB := compat_$(SCHEME_IMPL).scm

.PHONY: default
default: target/stage2.scm

target:
	mkdir -p target

COMPILER_SOURCES := \
	compiler/util.ml          \
	compiler/token.ml         \
	compiler/common_syntax.ml \
	compiler/ast.ml           \
	compiler/core.ml          \
	compiler/lex.ml           \
	compiler/parser.ml        \
	compiler/ctx.ml           \
	compiler/elab.ml          \
	compiler/compile.ml       \
	compiler/main.ml
TARGET_SOURCES := $(patsubst compiler/%.ml,target/%.ml,$(COMPILER_SOURCES))

$(TARGET_SOURCES): target/%.ml: compiler/%.ml | target
	cp $< $@

target/ocamlshim.cmx: ocamlshim.ml | target
	$(OCAMLC) -o $@ -c $<

target/stage1.exe: $(TARGET_SOURCES) target/ocamlshim.cmx
	$(OCAMLC) -o $@ -I target ocamlshim.cmx -open Ocamlshim $(TARGET_SOURCES)

target/stage2.scm: target/stage1.exe $(TARGET_SOURCES)
	$< $(TARGET_SOURCES) >target/tmp2.scm
	cp target/tmp2.scm $@

target/stage3.scm: target/stage2.scm $(TARGET_SOURCES) prelude.scm $(SCHEME_COMPAT_LIB)
	$(SCHEME_COMMAND) $< $(TARGET_SOURCES) >target/tmp3.scm
	cp target/tmp3.scm $@

target/stage4.scm: target/stage3.scm $(TARGET_SOURCES) prelude.scm $(SCHEME_COMPAT_LIB)
	$(SCHEME_COMMAND) $< $(TARGET_SOURCES) >target/tmp4.scm
	cp target/tmp4.scm $@

.PHONY: verify_fixpoint
verify_fixpoint: target/stage3.scm target/stage4.scm
	diff $^
	@printf "\x1b[32m""fixpoint successful!""\x1b[m""\n"

.PHONY: clean
clean:
	rm -rf target
