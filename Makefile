OCAMLC := ocamlopt
SCHEME_IMPL := chez

SCHEME_COMMAND_chicken := csi compat_chicken.scm prelude.scm -script
SCHEME_COMMAND_chez    := scheme --script compat_chez.scm

SCHEME_COMMAND    := $(SCHEME_COMMAND_$(SCHEME_IMPL))
SCHEME_COMPAT_LIB := compat_$(SCHEME_IMPL).scm

.PHONY: default
default: target/stage2.scm

target:
	mkdir -p target

target/%.ml: %.ml target
	cp $< $@

target/%.cmx: target/%.ml
	$(OCAMLC) -c $<

target/stage1.exe: target/main.ml target/ocamlshim.cmx
	$(OCAMLC) -o $@ -I target ocamlshim.cmx -open Ocamlshim $<

target/stage2.scm: target/stage1.exe main.ml
	$< main.ml > target/tmp2.scm
	cp target/tmp2.scm $@

target/stage3.scm: target/stage2.scm main.ml prelude.scm $(SCHEME_COMPAT_LIB)
	$(SCHEME_COMMAND) $< main.ml > target/tmp3.scm
	cp target/tmp3.scm $@

target/stage4.scm: target/stage3.scm main.ml prelude.scm $(SCHEME_COMPAT_LIB)
	$(SCHEME_COMMAND) $< main.ml > target/tmp4.scm
	cp target/tmp4.scm $@

.PHONY: verify_fixpoint
verify_fixpoint: target/stage3.scm target/stage4.scm
	diff $^
	@printf "\x1b[32m""fixpoint successful!""\x1b[m""\n"

.PHONY: clean
clean:
	rm -rf target
