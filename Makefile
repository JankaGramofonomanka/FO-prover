.PHONY: all

all: FO-prover

FO-prover:
	stack build --copy-bins

clean:
	rm FO-prover