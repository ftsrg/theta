# ANTLR-Based C-Frontend for Verification

This subproject adds an ANTLR-grammar based C-Frontend to Theta. This is independent of any formalism, and aims to be as widely applicable as possible.

## Features

This frontend can handle preprocessed .c or .i file with the following features:

* Basic C support: global declarations (functions and variables), function definitions, loops, various data types, global typedefs, etc.
* Integer- and bitvector-arithmetic support based on required features (e.g. for floats or bitwise operators bitvector precision is necessary)
* Basic struct and array support
* Basic (and experimental) flat-memory based pointer handling
* ILP32 and LP64 type system support (with possible extensibility)

## Limitations, known bugs

A number of features are either not well tested or in certain aspects buggy. Error handling is done on a best-effort level as the C specification is way too complex to handle entirely correctly. In most cases an error, or a warning message is displayed, but in some unexpected situations a silent failure is also possible.

In particular, the following features are either not implemented or can produce buggy models:

* Floating-point pointers (produces an exception when (de)referred)
* Structs including arrays and arrays including structs (produces an exception when accessed)
* Enums (only produces a warning, behaves as a normal signed int would)
* Unions (produces an exception when any element is accessed)
* Alignof, Sizeof, various extensions (produces a parsing exception)
* Pointer arithmetic (produces an exception)
* Using a non-specific subtype of `char` (produces a warning) - use `(un)signed char` instead
* Includes and other preprocessor directives (produces an exception or fails silently!)
* Arrays are not pointers and pointers cannot be used as arrays (produces an exception)
* Memory access is _not_ checked, and therefore it is easy to receive a faulty value by over-indexing an array (fails silently!)
* Array elements are not range-checked and therefore false positives are possible (consider `char c[2]; if(c[1] > 500) reach_error()`)

Note that only program elements that are (transitively) reachable from main() are checked against any violation of the above criteria, i.e. a program containing unsupported elements that are not utilized is handled correctly. This is necessary for handling most preprocessed (.i) files, as the standard library includes a lot of complex and unsupported code.

## High-Level Process

The workflow to get a formal model from a C file is the following:

1. Preprocess the C file
2. **Parse and transform the C file using this subproject**
3. Using the _IM_, build a formal model using a specialized visitor

## Structure of the _IM_

The _IM_ is an interlinked model of the following elements:

* CAssignment: variable assignment
* CAssume: an assumption over the range of a variable 
* CBreak: the _break_ C instruction
* CCall: function call to a C-type function
* CCase: a branch (_case_) of a switch-case statement 
* CCompound: a compound statement (0..* statements inside braces)
* CContinue: the _continue_ C instruction
* CDecls: variable declarations
* CDefault: the default branch of a switch-case statement
* CDoWhile: a do-while loop statement
* CExpr: a C expression
* CFor: a for loop statement
* CFunction: a function in the source
* CGoto: _goto_ statement
* CIf: a conditional branching statement
* CInitializerList: initializer list for arrays, structs and other complex structures
* CProgram: the root element 
* CRet: return statement from a function
* CSwitch: a switch-case statement
* CWhile: a while loop statement

To map these statements to elements of a formal model, the `hu.bme.mit.theta.frontend.transformation.model.statements.CStatementVisitorBase` class can be used through inheritance. An example can be found in `hu.bme.mit.theta.xcfa.model.utils.FrontendXcfaBuilder`.
