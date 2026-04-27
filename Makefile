.PHONY: all clean generate-teleportation-py generate-measure-send-py

all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf
	rm -rf extracted generated

%: CoqMakefile
	$(MAKE) -f CoqMakefile $@

generate-teleportation-py: examples/Teleportation.vo ocaml/write_apps.ml ocaml/generate_teleportation.ml python/qoreo_netqasm_runtime.py
	mkdir -p extracted generated
	ocamlc -I extracted -c extracted/teleportation_netqasm.mli
	ocamlc -I extracted -c extracted/teleportation_netqasm.ml
	ocamlc -I extracted -I ocaml -c ocaml/write_apps.ml
	ocamlc -I extracted -I ocaml -c ocaml/generate_teleportation.ml
	ocamlc -I extracted -I ocaml -o extracted/generate_teleportation unix.cma extracted/teleportation_netqasm.cmo ocaml/write_apps.cmo ocaml/generate_teleportation.cmo
	./extracted/generate_teleportation generated/teleportation

generate-measure-send-py: examples/MeasureSend.vo ocaml/write_apps.ml ocaml/generate_measure_send.ml python/qoreo_netqasm_runtime.py
	mkdir -p extracted generated
	ocamlc -I extracted -c extracted/measure_send_netqasm.mli
	ocamlc -I extracted -c extracted/measure_send_netqasm.ml
	ocamlc -I extracted -I ocaml -c ocaml/write_apps.ml
	ocamlc -I extracted -I ocaml -c ocaml/generate_measure_send.ml
	ocamlc -I extracted -I ocaml -o extracted/generate_measure_send unix.cma extracted/measure_send_netqasm.cmo ocaml/write_apps.cmo ocaml/generate_measure_send.cmo
	./extracted/generate_measure_send generated/measure_send
