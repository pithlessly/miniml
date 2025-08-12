OCAMLC := ocamlopt
SCHEME_IMPL := chez

SCHEME_COMMAND_chicken := csi compat_chicken.scm prelude.scm -script
SCHEME_COMMAND_chez    := scheme --script compat_chez.scm

SCHEME_COMMAND    := $(SCHEME_COMMAND_$(SCHEME_IMPL))
SCHEME_COMPAT_LIB := compat_$(SCHEME_IMPL).scm

.PHONY: default
default: target/compiled.scm

target:
	mkdir -p target

target/%.ml: %.ml target
	cp $< $@

target/%.cmx: target/%.ml
	$(OCAMLC) -c $<

target/main.exe: target/main.ml target/ocamlshim.cmx
	$(OCAMLC) -o $@ -I target ocamlshim.cmx -open Ocamlshim $<

target/compiled.scm: target/main.exe main.ml
	$< main.ml > target/tmp.scm
	cp target/tmp.scm $@

target/compiled2.scm: target/compiled.scm main.ml prelude.scm $(SCHEME_COMPAT_LIB)
	$(SCHEME_COMMAND) $< main.ml > target/tmp2.scm
	cp target/tmp2.scm $@

.PHONY: verify_bootstrapping
verify_bootstrapping: target/compiled2.scm target/compiled.scm
	diff $^
	@printf "\x1b[32m""bootstrapping successful!""\x1b[m""\n"

.PHONY: clean
clean:
	rm -rf target
