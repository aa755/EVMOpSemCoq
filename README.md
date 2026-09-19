self-contained EVM operational semantics in Coq, generated from [Yoichi's EVM semantics](https://github.com/pirapira/eth-isabelle) and [Lem](https://github.com/rems-project/lem)

The `step` function in `block.v` advances one whole-machine transition: an instruction or a call/return boundary. Repeated steps execute a transaction; `Continue` is not a terminal outcome.

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

The conversion implementation subsequently uses structural fuel to avoid
normalizing large well-founded proof terms during evaluation. Its fuel is the
input natural number. `boolListFromNatural_aux_fuel` proves independence of any
sufficient bound, and `boolListFromNatural_equation` proves the original halving
recurrence without a truncation assumption. These are closed proofs.

### Transaction outcomes

`start_transaction` now returns `Rejected reason original_state` for nonce,
funding, block gas-limit, or intrinsic-gas failure. Rejections are terminal and
never enter fee settlement. The old `nothing_happens` pseudo-execution is removed.
The existing transaction input represents an already authenticated sender;
signature decoding and block-wide validation remain outside this interface.

Completed executions carry `tr_result.f_outcome`, either
`ExecutionSuccess output` or `ExecutionFailure reasons`. Nested failure returns
zero to the caller and does not automatically fail the transaction. Top-level
failure restores the accepted checkpoint (including the prepaid fee and consumed
nonce), clears reverted substate, and consumes the remaining execution gas.

`settle_transaction tr block result` preserves the distinction through settlement:

- `Some (TransactionRejected reason state)` preserves the original state exactly.
- `Some (TransactionExecuted outcome state)` contains the outcome and the state
  after `end_transaction` applies refunds, destruction, and miner payment.
- `None` means execution is still running or encountered `Unimplemented`.

Root CREATE no longer resumes its synthetic caller after initcode termination.
Code-deposit failure is exceptional from Homestead onward; Frontier retains its
empty-code behavior. Successful root creation deposits code and terminates.
Empty initcode follows CREATE too, so the endowment is not skipped. Root failure
preserves the sender nonce increment. The selected `network` controls the
code-deposit rule; callers should supply block data consistent with that network.

API changes: users constructing `global.g_stack` must use `call_frame`, users
constructing `tr_result` must supply `f_outcome`, and exhaustive matches on
`global_state` must handle `Rejected`. Existing `end_transaction` remains the
low-level settlement function for an executed `tr_result`; callers processing
arbitrary startup/execution results should use `settle_transaction`.

`tests/Transactions.v` covers all four rejection causes, output and failure
propagation, root CREATE and code deposit, and fee/nonce settlement. In the
numerical settlement test, a balance of 100000 pays a fee of 30000: the sender
ends at 70000 with nonce 1, and the miner's balance increases by 30000.

### Reproducible verification

From this repository, in the intended switch environment:

```sh
opam exec --switch=evmni -- python3 scripts/check.py
```

Or from the parent project: `./scripts/in-switch ./EVMOpSem/scripts/check.py`.
The script builds both theories and tests, rejects active DAEMON/admitted holes,
checks the transitive operational assumptions against the two classical axioms
listed above, and runs `rocqchk` on every regression module and its dependencies.
Reports are written under `_build/`.

These changes repair the audited legacy paths; they are not a complete Ethereum
conformance proof or the requested non-interference proof. EIP-7702 is deferred,
precompiles are outside this task, and no REVERT opcode is added to the early-fork
model. `Unimplemented` remains explicit rather than being counted as success.
