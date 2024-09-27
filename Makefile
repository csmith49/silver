ocb_flags = -r -use-ocamlfind -pkgs 'containers, zarith, MenhirLib, Z3' -tag thread
ocb = ocamlbuild $(ocb_flags)

.phony: all
all: silver

silver: $(shell find src -type f)
	$(ocb) silver.native
	mv silver.native silver

.phony: clean
clean:
	rm -rf _build silver
