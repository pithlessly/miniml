OCAMLC := ocamlopt
SCHEME_IMPL := chicken

SCHEME_COMMAND_chicken := csi -s
SCHEME_COMMAND_chez    := scheme --script

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

scratchpad.mini-ml: main.ml
	cp $< $@

target/compat.scm: $(SCHEME_COMPAT_LIB)
	cp $< $@

target/compiled.scm: target/main.exe scratchpad.mini-ml
	$< > target/tmp.scm
	cp target/tmp.scm $@

target/compiled2.scm: target/compiled.scm prelude.scm target/compat.scm
	$(SCHEME_COMMAND) $< > target/tmp2.scm
	cp $< $@

.PHONY: verify_bootstrapping
verify_bootstrapping: target/compiled2.scm target/compiled.scm
	diff $^
	@printf "\x1b[32m""bootstrapping successful!""\x1b[m""\n"

.PHONY: clean
clean:
	rm -rf target
