.PHONY: all

all: FO-prover

FO-prover: FO-prover.hs *.hs
	ghc -o FO-prover FO-prover.hs

clean:
	rm FO-prover *.hi *.o