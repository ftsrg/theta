## What analysis steps mean in this case
These are simple "checks", executed while the IR is parsed into our representation (so we won't need to explicitly iterate through it twice).

### Struct check
Using an `llvm::Typefinder`, we check if there are any struct (or union) type definitions in the module. This information is then stored and can be queried.

### Logical operator check
This check is called for each instruction. The goal of this check is to decide, if Theta can use integer arithmetics or only the more costly bitwise arithmetics.

#### How it works
Steps executed on each instruction:
- Is it an `and/or/xor` operation?
    - If **yes**, is it only used later in `icmp` operations with 0 as the other operand?
        - If **yes**, *integer arithmetics* are suitable
        - If **no**, we'll need *bitwise arithmetics*
- Else, is it a shift (`shl/lshr/ashr`) operation?
    - If **yes**, we'll need *bitwise arithmetics*
    - If **no**, *integer arithmetics* are suitable

*Clarification: this is a global attribute in the sense, that if any instruction requires integer arithmetics, then the whole program has to be handled that way.*
