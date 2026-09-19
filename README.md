self-contained EVM operational semantics in Coq, generated from [Yoichi's EVM semantics](https://github.com/pirapira/eth-isabelle) and [Lem](https://github.com/rems-project/lem)

the `step` function in block.v is the top-level eval function. `step` does not fully evaluate a transaction: it only evaluates it to the next call. however, repeating `step` will finish the evaluation.

tested on 25 Sept 2024, 11am EST:

```
[abhishek@optiplex home-aut]$ docker pull coqorg/coq
Using default tag: latest
latest: Pulling from coqorg/coq
Digest: sha256:939bb94fcd61a28a9423ace6c25c6ffcb13fe902b00af78605d0f19d15c65495
Status: Image is up to date for coqorg/coq:latest
docker.io/coqorg/coq:latest
[abhishek@optiplex home-aut]$ docker run --name coqevm -d -ti coqorg/coq:latest; docker start coqevm; docker attach coqevm
5fb8ffb85238df5c6afe189823c7ff4c4b7d1c04feaa39d21a57008179f5c810
coqevm
coq@5fb8ffb85238:~$ git clone https://github.com/aa755/EVMOpSemCoq
Cloning into 'EVMOpSemCoq'...
remote: Enumerating objects: 60, done.
remote: Counting objects: 100% (60/60), done.
remote: Compressing objects: 100% (37/37), done.
remote: Total 60 (delta 22), reused 60 (delta 22), pack-reused 0 (from 0)
Receiving objects: 100% (60/60), 79.74 KiB | 1.05 MiB/s, done.
Resolving deltas: 100% (22/22), done.
coq@5fb8ffb85238:~$ cd EVMOpSemCoq/
coq@5fb8ffb85238:~/EVMOpSemCoq$ dune build # succeeds, but after too many warnings
```

## Local repair branch

The starting source snapshot was copied from
`~/fv-workspace/workspace/monad/monadproofs/EVMOpSem` on 2026-09-18.
The original workspace is not modified. This branch keeps the public repository
history and builds independently with Rocq 9.0.1 and its Stdlib.

From the parent project directory, run:

```sh
./scripts/in-switch dune build --root EVMOpSem
```

The named opam switch is `evmni`; it is not the default switch.

### Removing DAEMON

The upstream commit `a0c09b8` already identified the arbitrary-inhabitant axiom
as removable. The repair proves both halving termination obligations and gives
concrete defaults to the generated datatypes. `sum_default` now takes an
explicit inhabitant of its left summand; there is no total default for arbitrary
uninhabited sums.

`tests/Harness.v` checks both recursive functions and prints the transitive
assumptions of the instruction/whole-machine/transaction entry points and word
arithmetic. Word addition, integer conversion, and both recursions are closed;
the operational entry points retain only `Classical_Prop.classic` and
`Description.constructive_definite_description`. The generic Lem library still
contains unrelated abstract set operations; these do not appear in that closure.
Historical comments (including the deprecated, commented-out `evmfull.v`) are
not active declarations.

### Nested rollback

Call frames now save the destruction list alongside world state and the caller
context. CALL/CALLCODE, DELEGATECALL, and CREATE save this journal. Exceptional
return restores it. The same restoration is used when Homestead code deposit
runs out of gas; the previous branch restored world state but imported the
failed initcode's logs/refund and retained its destruction list.

`tests/Rollback.v` checks an actual five-step suffix: C's pending SELFDESTRUCT,
B's invalid instruction and exceptional return, then A's STOP and successful
completion. Before the repair it retained C; afterwards it preserves precisely
the destruction list from before B's call. A successful B preserves C instead.
Additional quantified checks cover saved world, storage, gas, logs and refunds,
and code-deposit failure. This is a machine-level regression, not a proof that
all transaction semantics agrees with Ethereum.
