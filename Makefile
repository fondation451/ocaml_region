_SHELL      := bash
TARGET     := main.native
SQUALLC    := rcaml
OCAMLBUILD :=\
  ocamlbuild \
    -classic-display \
    -j 4 \
    -use-ocamlfind \
    -use-menhir \
    -menhir "menhir --infer --explain -v" \

.PHONY: all clean

all:
	@ $(OCAMLBUILD) -quiet $(TARGET)
	@ ln -sf $(TARGET) $(SQUALLC)

clean:
	rm -f *~
	rm -f tests/*.rq
	$(OCAMLBUILD) -clean
	rm -f $(TARGET) $(SQUALLC)
