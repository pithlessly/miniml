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

.PHONY: run
run: target/compiled.scm prelude.scm
	$(SCHEME) $<
