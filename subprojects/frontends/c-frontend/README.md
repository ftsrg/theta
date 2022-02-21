# ANTLR-Based C-Frontend for Verification

This subproject contains a C ANTLR grammar and related classes to parse preprocessed C files and transform the AST into an interlinked model of semantic elements (_IM_).

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
