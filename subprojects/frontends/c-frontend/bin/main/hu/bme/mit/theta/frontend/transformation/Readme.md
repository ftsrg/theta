# Antlr-based C frontend

This package is responsible for the transformation of C language programs to formal models. The
overview of this process is the following:

1. The C file (.c/.h/.i) is parsed by the following classes:
    1. FunctionVisitor - this provides CStatements, such as CPrograms, CFunctions and regular C-like
       statements (assignments, function calls, etc)
    2. TypeVisitor - this provides CType information, such as ints, enums, floats, arrays, etc.
    3. ExpressionVisitor - this provides Theta Expr<?> instances that represent expressions in the
       source file
    4. DeclarationVisitor - this provides CDecl instances, which provide information on declared
       variables
2. The topmost CStatement (a CProgram instance) can be _built_, i.e. transformed into a formal
   model. This will recursively instantiate parts of the model until all statements are consumed.
