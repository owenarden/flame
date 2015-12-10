FSTAR_HOME=/usr/local/opt/fstar
LIB=$(FSTAR_HOME)/libexec/stdlib
BIN=$(FSTAR_HOME)/bin
FSTAR=fstar.exe --include "/usr/local/opt/fstar/stdlib" --prims prims.fst --debug_level Extreme
#--include /usr/local/Cellar/fstar/0.9.1.1/stdlib --prims prims.fst

all: out Flame.ml

%.ml : %.fst
	$(FSTAR) --odir out --codegen OCaml $<
	cp $(LIB)/ml/prims.ml $(LIB)/ml/FStar_IO.ml out

%.o : %.ml
	(cd out; ocamlc -o $@ prims.ml FStar_IO.ml $<)
#	./out/flame.exe

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
