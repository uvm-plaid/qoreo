PYTHON_GENERATION_EXAMPLES := \
	MeasureSend \
	B92 \
	DQFT \
	UnitaryTest \
	Teleportation \
	ConditionalTest \
	DistributedGrover

ocaml_module = $(shell printf '%s' '$1' | awk '{ if ($$0 ~ /^[A-Z]+$$/) print substr($$0, 1, 1) tolower(substr($$0, 2)); else print }')

.PHONY: all clean clean-generated $(PYTHON_GENERATION_EXAMPLES) examples

all: CoqMakefile
	$(MAKE) -f CoqMakefile

examples: $(PYTHON_GENERATION_EXAMPLES)

proofs: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

ocaml/write_apps.cmo: ocaml/write_apps.ml
	ocamlc -I extracted -I ocaml -c $<

clean: CoqMakefile clean-generated
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf
	rm -rf extracted

clean-generated:
	rm -rf generated
	rm -f extracted/*.cmi extracted/*.cmo extracted/generate_*

%: CoqMakefile
	$(MAKE) -f CoqMakefile $@

$(PYTHON_GENERATION_EXAMPLES): %: \
	src/Examples/%.vo \
	ocaml/write_apps.cmo \
	ocaml/generate_apps.ml \
	python/qoreo_netqasm_runtime.py \
	python/qoreo_netsquid_runtime.py
	mkdir -p extracted generated
	ocamlc -I extracted -c -o extracted/$(call ocaml_module,$*).cmi extracted/$*.mli
	ocamlc -I extracted -c -o extracted/$(call ocaml_module,$*).cmo extracted/$*.ml
	cp ocaml/generate_apps.ml extracted/generate_$*.ml
	ocamlc -I extracted -I ocaml -open $(call ocaml_module,$*) -c extracted/generate_$*.ml
	ocamlc -I extracted -I ocaml -o extracted/generate_$* unix.cma extracted/$(call ocaml_module,$*).cmo ocaml/write_apps.cmo extracted/generate_$*.cmo
	./extracted/generate_$* generated/$*
