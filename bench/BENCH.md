Benchmarking
------------

TODO: Add instructions for benchmarking on systems without the Nix package manager.

Benchmarking (Nix)
------------------

#### Build HVM

See [NIX.md](../NIX.md#usage-nix) in the root directory for instructions.

#### Initialise development shell

```sh
cd ..       # Go back to the root HVM directory.
nix develop # Initialise the dev shell. The rest of the instructions in this section assume that you're using the dev shell.
cd bench
cd <benchmark_directory>
```

#### Benchmark Haskell code:

```sh
ghc -O2 main.hs -o main
hyperfine --show-output ./main
```

#### Benchmark HVM code:

```sh
../../result/bin/hvm compile main.hvm
clang -O2 main.c -o main -lpthread
hyperfine --show-output ./main
```