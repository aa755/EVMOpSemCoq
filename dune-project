(lang dune 3.21)
(using rocq 0.11)
(name rocq-evm-op-sem)
(generate_opam_files)

(package
 (name rocq-evm-op-sem)
 (synopsis "EVM operational semantics generated from eth-isabelle and Lem")
 (depends rocq-core rocq-stdlib))

(source (github aa755/EVMOpSemCoq))
