OPT=0

all:
	ghc --make -O$(OPT) -o cubical Main.hs

bnfc:
	bnfc --haskell -d Raw.cf
	happy -gca Raw/Par.y
	alex -g Raw/Lex.x
	ghc --make -O$(OPT) Raw/Test.hs -o Raw/Test

clean:
	rm -f *.log *.aux *.hi *.o cubical
	cd Raw && rm -f ParRaw.y LexRaw.x LexhRaw.hs \
                        ParRaw.hs PrintRaw.hs AbsRaw.hs *.o *.hi

