## Passes used
### About LLVM passes in general
Passes provide a system to run optimization, transformation and analysis steps on LLVM IR. These can be LLVMs official passes, but custom passes as well. This project uses both.
[more on LLVM passes](https://llvm.org/docs/Passes.html)

This part of the project adopts the most from Gazer. LLVM and custom passes are used there similarly as well, although Gazer has a more complex and less naive approach, e.g. using early and late optimization sets. In this project we are approaching the problems and functionality in a direct manner, thus we have only a simpler, single execution line of passes.

### What are we using passes for
1. Optimizations
2. Transformations 
3. Annotations

*Disclaimer: this part of the project isn't static, as we are constantly experimenting with changing/adding new passes. Due to this, some important custom passes are described here, but to get the precise state of what passes we use and what they do, start from [this](https://github.com/ftsrg/theta-c-frontend/blob/master/src/utilities/CPipeline.cpp) source file.*
### Custom passes
- **Toposort pass**
    Strongly connected components (e.g. loops) of basic blocks aren't necessarily in topological order in LLVM IR as this way it is possible to iterate through the blocks in order and have unknown values only in phi nodes, which makes the model transformation in Theta simpler
- **Eliminate GEP instructions pass**
    The getelementptr instruction is a special instruction in LLVM IR, which usually pairs with one or more store and load instructions to get/set memory values. In the XCFA this instruction pair is handled as a single instruction on a single edge, but transforming to this format is complex. Instead of that we use this transformation pass to combine the information from these pairs into a single `theta.dbg.getArrayElement_typename` or `theta.dbg.setArrayElement_typename` function calls while removing the `getelementptr` and `load/store` instructions. *Support in this pass is currently incomplete, as there can be special parametrizations in these instructions when structs or unions are used, so that has to be added when extending the frontend with struct support in the future.*    
- **Eliminate Phi nodes pass**
    When verifying a model with CEGAR, the number of variables can be a crucial point. Phi nodes can basically add a variable per each node, although it wasn't present in the original program and wouldn't be necessary. This pass eliminates these unnecessary variables, where possible and uses a global variable with unique identifiers to store these values instead.
- **Branch dbg call pass** *(work in progress)*
    This pass adds a function called `theta.dbg.control` before each `br` *(branch)* instruction. On one hand, adding metadata to this call will make it easier to add *control* information to witnesses, on the other hand it tones down the CFG simplification pass, which is an important optimization, but can also be quite aggressive when merging control flow branches with which we lose *(or even get wrong)* program line metadata. False information on program lines can lead to unusable witnesses.
