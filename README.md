# Idris2-HVM

Code generator for [Idris 2](https://github.com/idris-lang/Idris2) producing [Higher-Order Virtual Machine (HVM)](https://github.com/HigherOrderCO/HVM) IR.

Currently not implemented:
- FFI
- External primitive operations 
- Many primitive functions and types (int and integer for example)

### Building

1. Install the Idris 2 and idris2api
2. `idris2 --build idris2-hvm.ipkg`
3. Add ./build/exec/idris2-hvm to PATH or use an alias

### Using

Compile module to HVM:

`idris2-hvm Main.idr -o main`

Execute specific function from module using the HVM interpreter:

`idris2-hvm --exec main Main.idr`
