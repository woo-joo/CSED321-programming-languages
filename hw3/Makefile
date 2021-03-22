CAMLC	 	  = ocamlc
CAMLOPT		= ocamlopt
CAMLCFLAG = -thread 
CAMLDEP=ocamldep

CAMLYACC=ocamlyacc
YACCFLAGS=-v
CAMLLEX=ocamllex

TARGET = hw3test
OBJ = common.cmo hw3.cmo hw3sol.cmo hw3test.cmo

all: $(OBJ)
	$(CAMLC) -thread -o $(TARGET) unix.cma threads.cma $(OBJ) 

clean:
	rm -f $(TARGET) *.annot *.aux *.log *.cm[iox] *.dvi 

.SUFFIXES : .ml .mli .cmo .cmi .cmx 

.ml.cmo: $<
	$(CAMLC) $(CAMLCFLAG) -c $< -o $@
.ml.cmx: $<
	$(CAMLOPT) $(CAMLCFLAG) -c $< -o $@
.mli.cmi: $<
	$(CAMLC) $(CAMLCFLAG) -c $< -o $@

depend: 
	$(CAMLDEP) *.mli *.ml > .depend 

.PHONY: depend

include .depend
