gt: grammar.cmo parse.cmo lex.cmo dump.cmo dump_mlcf_pp.cmo dump_mlcf_eq.cmo main.cmo Makefile
	ocamlc -o gt util.cmo trie.cmo grammar.cmo parse.cmo lex.cmo dump.cmo dump_mlcf_pp.cmo dump_mlcf_eq.cmo main.cmo

emitted:
	$(MAKE) -f most_recent_emitted_Makefile

main.cmo: main.ml parse.cmo lex.cmo
	ocamlc -c main.ml

grammar.cmo: grammar.ml trie.cmo
	ocamlc -c grammar.ml

util.cmo: util.ml
	ocamlc -c util.ml

dump.cmo: dump.ml grammar.cmo
	ocamlc -c dump.ml

dump_mlcf_pp.cmo: dump_mlcf_pp.ml grammar.cmo
	ocamlc -c dump_mlcf_pp.ml

dump_mlcf_eq.cmo: dump_mlcf_eq.ml grammar.cmo
	ocamlc -c dump_mlcf_eq.ml

trie.cmo: trie.ml
	ocamlc -c trie.ml

lex.cmo: parse.ml lex.ml
	ocamlc -c lex.ml

parse.cmo: parse.ml parse.cmi
	ocamlc -c parse.ml

parse.cmi: parse.mli
	ocamlc -c parse.mli

parse.mli parse.ml: grammar.cmo util.cmo parse.mly
	ocamlyacc -v parse.mly

lex.ml: lex.mll parse.cmi
	ocamllex lex.mll

clean:
	rm -f lex.ml parse.mli parse.ml parse.output *.cmo *.cmi gt

