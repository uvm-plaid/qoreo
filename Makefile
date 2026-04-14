.PHONY: all clean extract

all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf
	rm -f src/ExtractEpp.glob src/ExtractEpp.vo src/ExtractEpp.vok src/ExtractEpp.vos
	rm -rf extracted

%: CoqMakefile
	$(MAKE) -f CoqMakefile $@

extract: src/Network.vo src/ExtractEpp.v
	mkdir -p extracted
	rocq compile -Q src Qoreo src/ExtractEpp.v
