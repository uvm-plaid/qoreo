PYTHON_GENERATION_TARGETS := \
	generate-measure-send-py \
	generate-b92-py \
	generate-dqft-py \
	generate-unitary-py \
	generate-teleportation-py

.PHONY: all clean $(PYTHON_GENERATION_TARGETS) examples

all: CoqMakefile
	$(MAKE) -f CoqMakefile

examples: $(PYTHON_GENERATION_TARGETS)

proofs: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

clean: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf
	rm -rf extracted generated

%: CoqMakefile
	$(MAKE) -f CoqMakefile $@

generate-teleportation-py: EXTRACTED_MODULE = teleportation_netqasm
generate-teleportation-py: GENERATOR = teleportation
generate-teleportation-py: OUTPUT_DIR = teleportation
generate-teleportation-py: src/Examples/Teleportation.vo ocaml/generate_teleportation.ml python/qoreo_netqasm_runtime.py

generate-measure-send-py: EXTRACTED_MODULE = measure_send_netqasm
generate-measure-send-py: GENERATOR = measure_send
generate-measure-send-py: OUTPUT_DIR = measure_send
generate-measure-send-py: src/Examples/MeasureSend.vo ocaml/generate_measure_send.ml python/qoreo_netqasm_runtime.py

generate-b92-py: EXTRACTED_MODULE = b92_netqasm
generate-b92-py: GENERATOR = b92
generate-b92-py: OUTPUT_DIR = b92
generate-b92-py: src/Examples/B92.vo ocaml/generate_b92.ml python/qoreo_netqasm_runtime.py

generate-dqft-py: EXTRACTED_MODULE = dqft_netqasm
generate-dqft-py: GENERATOR = dqft
generate-dqft-py: OUTPUT_DIR = dqft
generate-dqft-py: src/Examples/dis_qft.vo ocaml/generate_dqft.ml python/qoreo_netsquid_runtime.py

generate-unitary-py: EXTRACTED_MODULE = unitary_test_netqasm
generate-unitary-py: GENERATOR = unitary
generate-unitary-py: OUTPUT_DIR = unitary_test
generate-unitary-py: src/Examples/unitary_test.vo ocaml/generate_unitary.ml python/qoreo_netsquid_runtime.py


generate-conditional-py: EXTRACTED_MODULE = conditional_test_netqasm
generate-conditional-py: GENERATOR = conditional
generate-conditional-py: OUTPUT_DIR = conditional
generate-conditional-py: src/Examples/conditional_test.vo ocaml/generate_conditional_test.ml python/qoreo_netquid_runtime.py


$(PYTHON_GENERATION_TARGETS): generate-%-py: ocaml/write_apps.ml
	mkdir -p extracted generated
	ocamlc -I extracted -c extracted/$(EXTRACTED_MODULE).mli
	ocamlc -I extracted -c extracted/$(EXTRACTED_MODULE).ml
	ocamlc -I extracted -I ocaml -c ocaml/write_apps.ml
	ocamlc -I extracted -I ocaml -c ocaml/generate_$(GENERATOR).ml
	ocamlc -I extracted -I ocaml -o extracted/generate_$(GENERATOR) unix.cma extracted/$(EXTRACTED_MODULE).cmo ocaml/write_apps.cmo ocaml/generate_$(GENERATOR).cmo
	./extracted/generate_$(GENERATOR) generated/$(OUTPUT_DIR)


generate-grover-py: examples/distributed_grover.vo ocaml/write_apps.ml ocaml/generated_dgro.ml python/qoreo_netsquid_runtime.py
	mkdir -p extracted generated
	ocamlc -I extracted -c extracted/distributed_grover_netqasm.mli
	ocamlc -I extracted -c extracted/distributed_grover_netqasm.ml
	ocamlc -I extracted -I ocaml -c ocaml/write_apps.ml
	ocamlc -I extracted -I ocaml -c ocaml/generated_dgro.ml
	ocamlc -I extracted -I ocaml -o extracted/generate_dgro unix.cma extracted/distributed_grover_netqasm.cmo ocaml/write_apps.cmo ocaml/generated_dgro.cmo
	./extracted/generate_dgro generated/grover

