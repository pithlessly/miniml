OCAMLC := ocamlc
SCHEME := csi -s

target/main.exe: target/main.ml
	$(OCAMLC) $< -o $@

target/%.ml: %.ml target
	cp $< $@

target:
	mkdir -p target

target/compiled.scm: target/main.exe scratchpad.mini-ml
	$< > target/tmp.scm
	cp target/tmp.scm $@

target/compiled2.scm: target/compiled.scm prelude.scm
	$(SCHEME) $< >$@

.PHONY: run, verify_bootstrapping
run: target/compiled2.scm
verify_bootstrapping: target/compiled2.scm target/compiled.scm
	diff $^
	@printf "\x1b[32m""bootstrapping successful!\x1b[m\n"
