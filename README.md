# Proving Cutoff Bounds for Safety Properties in First-Order Logic  
**`<Raz Lotan, Eden Frenkel, Sharon Shoham>`**

The method implemented in this tool gets as input a first-order transition system and an encoding of a size-reducing simulation which serves as a proof of a cutoff. The method generates a set of verification conditions and validates them using the Z3 SMT-solver, which either succeeds, or fails with a counterexample to some verification condition. The implementation includes the examples we verified and also allows the user to encode and verify new examples. 

### Quickstart

The repository for this artifact is available [online](https://github.com/Lotan-Raz/Proving-Cutoff-Bounds-for-Safety-Properties-in-First-Order-Logic) and can be cloned by running:

```
git clone https://github.com/Lotan-Raz/Proving-Cutoff-Bounds-for-Safety-Properties-in-First-Order-Logic.git
```

After making sure all requirements are satisfied, the experiments detailed in this README file can be run inside the repository's folder directly using Python 3.

#### Requirements

Our repository is a fork of [mypyvy](https://github.com/wilcoxjay/mypyvy) and has identical requirements. See mypyvy's [README file](https://github.com/wilcoxjay/mypyvy/blob/master/README.md) for more details.

# Verifying a cutoff




#### Verifying Examples

To verify an example, run:

```bash
python src/mypyvy.py verify-cutoff examples/cutoffs/TreeTermination.pyv
```

The tool automatically detects the given cutoff and μ-update, then validates the seven verification conditions. 

The expected output is:

```
Detected cutoff:
    sort = node
    bound = 2

Detected μ-update:
    condition(z:node) = root != z & node_sk != z
    update child(x:node, y:node, z:node) : bool = child(x, y) | child(x, z) & child(z, y)
    update ack(x:node, y:node, z:node) : bool = ack(x, y) | ack(x, z) & child(z, y) | child(x, z) & ack(z, y)
    update root(cand:node) : node = root
    update node_sk(cand:node) : node = node_sk
    update leq(node_1:node, node_2:node, cand:node) : bool = leq(node_1, node_2)
    update termd(node_1:node, cand:node) : bool = termd(node_1)


Running checks:

ι-preservation:
    Γ^h & ι^h & ν(z) => [ι^l]\z
    ... ok

μ-initiation:
    Γ & size > 2 & ι => exists z. μ(z)
    ... ok

μ-consecution:
    Γ & Γ' & μ(z) & τ => μ(z)'
    ... ok

Γ-preservation:
    Γ^h & ν(z) => [Γ^l]\z
    ... ok

projectability:
    Γ^h & ν(z) => closed(z)^l
    ... ok

τ-preservation:
    Γ^h & Γ^h' & ν(z) & ν'(z) & τ^h => [τ^l | τ0^l]\z
    ... ok

!φ-preservation:
    Γ^h & !φ^h & ν(z) => [!φ^l]\z
    ... ok

all ok!
```

If all verification conditions are valid, the output ends with `all ok!` (see above expected output for TreeTermination), otherwise the verification stops at the first failed check, and ends with `failed!`.

As an example of a failed check you can run:

```bash
python src/mypyvy.py verify-cutoff examples/cutoffs/PlusMinus_Error.pyv
```

#### Additional Options

Adding the flag `--verbose` will print the full queries sent to the solver. For instance run:

```bash
python src/mypyvy.py verify-cutoff --verbose examples/cutoffs/PlusMinus_Error.pyv
```

Adding the flag `--print-cex` prints counterexamples in case of failures. For instance, the expected output for:

```bash
python src/mypyvy.py verify-cutoff --print-cex examples/cutoffs/PlusMinus_Error.pyv
```
is the following
```
Detected cutoff:
    sort = node
    bound = 1

Detected μ-update:
    condition(z:node) = node_sk != z & (forall N:node. loc0(N) | loc1(N)) & (forall N:node. !(loc0(N) & loc1(N)))
    update x(cand:node) : int = x
    update node_sk(cand:node) : node = node_sk
    update loc0(node_1:node, cand:node) : bool = loc0(node_1)
    update loc1(node_1:node, cand:node) : bool = loc1(node_1)


Running checks:

ι-preservation:
    Γ^h & ι^h & ν(z) => [ι^l]\z
    ... ok

μ-initiation:
    Γ & size > 1 & ι => exists z. μ(z)
    ... ok

μ-consecution:
    Γ & Γ' & μ(z) & τ => μ(z)'
    ... ok

Γ-preservation:
    Γ^h & ν(z) => [Γ^l]\z
    ... ok

projectability:
    Γ^h & ν(z) => closed(z)^l
    ... ok

τ-preservation:
    Γ^h & Γ^h' & ν(z) & ν'(z) & τ^h => [τ^l | τ0^l]\z

========== COUNTER-EXAMPLE ==========
universes:
  sort node
    node0
    node1

immutable:
  node_sk = node1
  node_sk_l = node1

state 0:
  x = 0
  x_l = 0
  loc0(node0)
  loc0_l(node0)
  loc1(node1)
  loc1_l(node1)

state 1:
  x = 1
  x_l = 1
  loc1(node0)
  loc1(node1)
  loc1_l(node0)
  loc1_l(node1)
=====================================
    ... fail

failed!
```

The counterexamples are given in the format of mypyvy which gives the pre-state as `state 0` and the post-state as `state 1`. The low states are captured by constants, variables and functions that end with the suffix `_l`, and the high states are captured by the names without a suffix. For verification conditions that only consider one pair of high and low states, only `state 0` will appear.

#### Writing new Examples

Our implementation is built on top of mypyvy and uses its syntax. To write new examples, use mypyvy syntax — we refer to https://github.com/wilcoxjay/mypyvy for more information.

To encode a μ-update for an example at hand use the following keywords extending mypyvy's syntax:

- `cutoff sort` - to indicate the sort for which we find a cutoff.
- `cutoff bound` - to indicate the bound.
- `cutoff condition` - to indicate the deletion condition for the μ-update.
- `cutoff update` - to give an update term or formula.
- `cutoff hint` - to give a hint for verification condition (2).

Only `cutoff sort` is mandatory. Every other command may be omitted and in that case the appropriate construct will get a default value, as described in the paper. See the many examples under `~/mypyvy-cutoff/examples/cutoffs` for a demonstration of this syntax.

For instance, in the example TreeTermination, the following keywords can be used (some of these are the same as the deafult values, and so appear in comments in the file).

```
cutoff sort node

cutoff bound 2

cutoff update child(x: node, y: node, z: node) : bool =
  child(x,y) | (child(x,z) & child(z,y))

cutoff condition(z: node) =
  z != node_sk & z != root

cutoff hint terminate_node(n: node, n_l: node, z: node) =
  n = n_l
```

We invite users to declare a cutoff and encode a μ-update for the example ClientServer. A file with the protocol without an encoding of a μ-update is available at `ClientServer_empty.pyv`. The filled-in example is `ClientServer_full.pyv`. We also invite you to try and change the given μ-update in different ways (removing the update, removing the invariant, removing the hint, changing the bound, etc.) and see whether the verification succeeds or fails.
