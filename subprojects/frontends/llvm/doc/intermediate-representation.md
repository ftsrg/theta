## Intermediate representation between LLVM IR and the XCFA models
As we can see in the architecture, the C input program is compiled into LLVM IR. LLVM intermediate representation is an assembly-like representation with around 60 instructions and lots of possibilities for adding metadata. 

It can be easily parsed through the LLVM API, but contains a large quantity of complex information, from which we only need to extract particular elements required for the XCFA and the projection of counterexamples on to the original program. To accomplish this we use a simpler representation, which is in many points similar to the programmatic representation of LLVM IR, but differs in some particular places and contains no superfluous data (from our standpoint).

The classes for this representation can be found in the [types](https://github.com/ftsrg/theta-c-frontend/tree/master/src/types) directory.

It is similar to LLVM IR in that there is a module, which contains global variables and functions. Functions contain basic blocks, basic blocks are made of instructions, which have operands. It differs in that there are no explicit metadata classes, rather the above mentioned classes contain metadata about themselves. 

Furthermore on instruction level the LLVM IR has no classes explicitly representing (virtual) registers and instruction operands - these are handled as instructions, constants or other appropriate types. In our representation instruction contains Operands, an abstract class and parent class of Register, BasicBlockOperand and StringOperand. The latter is used to handle function operands in `call` instructions and special strings like the condition code in `icmp` operations.
