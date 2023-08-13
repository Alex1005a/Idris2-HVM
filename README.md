# Idris2-HVM

Code generator for [Idris 2](https://github.com/idris-lang/Idris2) producing [Higher-Order Virtual Machine (HVM)](https://github.com/HigherOrderCO/HVM) IR.

Currently not implemented:
- FFI
- External primitive operations 
- Many primitive functions and types (int and integer for example)

### Building

1. Install the Idris 2 and idris2api
2. `idris2 --build idris2-hvm.ipkg`
