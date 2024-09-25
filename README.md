self-contained EVM operational semantics in Coq, generated from [Yoichi's EVM semantics](https://github.com/pirapira/eth-isabelle) and [Lem](https://github.com/rems-project/lem)


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
