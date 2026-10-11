# Dynamic Subtree Mode

## Overview

Official implementation of "Nearly-Optimal Dynamic Subtree Mode". This repository provides two C implementations:

- **DSM** (`dsm.c`): leaf recoloring and subtree mode queries on a fixed tree.
- **FDSM** (`fdsm.c`): the few-color variant with recoloring, queries, subtree moves, and leaf insertion/deletion.

## Requirements

- A C11 compiler, such as GCC or Clang.
- The standard C library and math library. No third-party dependencies are required.

## Compilation

The files expose C functions and do not contain a `main` function. Compile them as objects:

```sh
cc -std=c11 -O3 -c dsm.c -o dsm.o
cc -std=c11 -O3 -c fdsm.c -o fdsm.o
```

Link either or both with your program, including `-lm`:

```sh
cc -std=c11 -O3 example.c dsm.o fdsm.o -lm -o example
```

## Datasets

The datasets are available on [Google Drive](https://drive.google.com/drive/folders/1uBWgV0RixuY1MlKCYvJBI_eFpVNiEEwD).

## Execution

Initialize the tree with `dsm_init` or `fdsm_init`, then call the corresponding update and query functions. FDSM also supports subtree moves and leaf insertion/deletion; call `dsm_destroy` or `fdsm_destroy` when finished.
