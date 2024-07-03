@echo off
python src/mypyvy.py verify-cutoff examples/cutoffs/TreeTermination.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/EchoMachine_round.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/EchoMachine_value.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/ToyConsensus_value.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/ToyConsensus_quorum.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/ToyConsensus_node.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/LockServer.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/ListToken.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/PlusMinus.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/EqualSum_thread.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/EqualSum_index.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/EqualSumOrders_thread.pyv
python src/mypyvy.py verify-cutoff examples/cutoffs/EqualSumOrders_index.pyv
pause
