## Compilation

1. Download [SoPlex](https://soplex.zib.de).
2. Compile to static library files `libsoplex.a` and `libsoplex_debug.a` and copy these over the placeholders in `source/lib` directory
3. run `make release` or `make debug` in the `source` directory

## Usage

`./roundingsat_lp --help` displays solver usage.
E.g., `./roundingsat_lp --lp=1 somefile.opb` solves `somefile.opb` using with the LP solver activated.
