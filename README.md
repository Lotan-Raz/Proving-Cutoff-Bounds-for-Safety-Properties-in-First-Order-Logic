The implementation of the results of the paper:

Proving Cutoff Bounds for Safety Properties in First-Order Logic / Raz Lotan, Eden Frenkel, Sharon Shoham

The implementation is built on top of mypyvy, and examples are written in that syntax:
https://github.com/wilcoxjay/mypyvy
Readers are referred to the tool paper: mypyvy: A Research Platform for Verification of Transition Systems in First-Order Logic
James R. Wilcox, Yotam M. Y. Feldman, Oded Padon and Sharon Shoham / CAV2024 for more information.

## Verifying a cutoff

To verify a cutoff bound for some file you do:
python src/mypyvy.py verify-cutoff examples/cutoffs/TreeTermination.pyv

mypyvy recognizes the given cutoff and mu-update 
```
DETECTED CUTOFF:
    bound node 2
    condition(z:node) = root != z & node_sk != z
    update child(x:node, y:node, z:node) : bool = child(x, y) | child(x, z) & child(z, y)
    update ack(x:node, y:node, z:node) : bool = ack(x, y) | ack(x, z) & child(z, y) | child(x, z) & ack(z, y)

Running checks:

INIT PRESERVATION:
    axioms^h & init^h & ν(z) => [init^l]\z
    ... PASSED

TRANSITION PRESERVATION:
    axioms^h & axioms^h' & ν(z) & ν'(z) & transitions^h => [transitions^l | idle^l]\z
    ... PASSED

FAULT PRESERVATION:
    axioms^h & !satefy^h & ν(z) => [!satefy^l]\z
    ... PASSED

PROJECTABILITY:
    axioms^h & ν(z) => closed(z)^l
    ... PASSED

Γ-PRESERVATION:
    axioms^h & ν(z) => [axioms^l]\z
    ... PASSED

μ-INITIATION:
    axioms & size > 2 & init => exists z. μ(z)
    ... PASSED

μ-CONSECUTION:
    axioms & axioms' & μ(z) & transitions => μ(z)'
    ... PASSED

all ok!
```


## Encoding a size-reducing simulation

Our implementation allows a user to encode a size-reducing simulation in the form of a mu-update, using the following commands:
cutoff sort [#sort] declares the sort for which we want to find a cutoff
cutoff bound [k] declares 

```
python3 src/mypyvy.py verify examples/lockserv.pyv
checking init:
  implies invariant mutex... ok. (0:00:00.000176)
  ...
checking transation send_lock:
  preserves invariant mutex... ok. (0:00:00.000120)
  preserves invariant on line 109... ok. (0:00:00.000107)
  ...
...
all ok!
```
