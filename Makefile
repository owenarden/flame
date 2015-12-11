FSTAR_HOME=/usr/local/opt/fstar
LIB=$(FSTAR_HOME)/libexec/stdlib
BIN=$(FSTAR_HOME)/bin
FSTAR=fstar.exe --include "/usr/local/opt/fstar/stdlib" --prims prims.fst --debug_level Extreme

OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g -w -8
#--include /usr/local/Cellar/fstar/0.9.1.1/stdlib --prims prims.fst

all: flame 

flame: out
	$(FSTAR) --odir out --codegen OCaml Flame_FLAM.fst
	$(FSTAR) --odir out --codegen OCaml Flame_IFC.fst
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml $(LIB)/ml/FStar_Set.ml $(LIB)/ml/FStar_ST.ml $(LIB)/ml/FStar_All.ml out
	(cd out; $(OCAMLOPT) -o Flame.o prims.ml FStar_IO.ml FStar_Set.ml FStar_ST.ml FStar_All.ml Flame_FLAM.ml Flame_IFC.ml)

#%.o : %.ml
#	./out/flame.exe

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
