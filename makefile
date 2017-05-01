all: interp

interp: Hw7.hs
	ghc -o interp -main-is Hw7.main Hw7.hs

clean: 
	rm -rf *.o *.hi interp

