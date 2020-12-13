python3 sema-gen.py data-latest.xml intrinsics.all.sema 16
python3 lift_sema.py
python3 gen_rules.py alu.lifted perf.json Skylake
