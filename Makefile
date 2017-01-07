all:
	happy -gca Pargrammar.y
	alex -g Lexgrammar.x
	latex Docgrammar.tex; dvips Docgrammar.dvi -o Docgrammar.ps
	ghc --make Testgrammar.hs -o Testgrammar
	ghc --make interpreter.hs
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f Docgrammar.ps
distclean: clean
	-rm -f DocGrammar.* LexGrammar.* ParGrammar.* LayoutGrammar.* SkelGrammar.* PrintGrammar.* TestGrammar.* AbsGrammar.* TestGrammar ErrM.* SharedString.* grammar.dtd XMLGrammar.*

