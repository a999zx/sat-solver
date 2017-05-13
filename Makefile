PROGRAM = sat_solver

$(PROGRAM): $(PROGRAM).ml
		ocamlopt -o $(PROGRAM) str.cmxa $(PROGRAM).ml

clean:
		rm -f $(PROGRAM) $(PROGRAM).cmi $(PROGRAM).cmx $(PROGRAM).o
