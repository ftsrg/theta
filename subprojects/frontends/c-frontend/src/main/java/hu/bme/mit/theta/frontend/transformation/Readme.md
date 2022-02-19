# Antlr-based C frontend

This package is responsible for the transformation of C language programs to XCFAs. The overview of this process is the following:

1. The C file (.c/.h/.i) is parsed by the following classes:
    1. FunctionVisitor - this provides CStatements, such as CPrograms, CFunctions and regular C-like statements (assignments, function calls, etc)
    2. TypeVisitor - this provides CType information, such as ints, enums, floats, arrays, etc.
    3. ExpressionVisitor - this provides Theta Expr<?> instances that represent expressions in the source file
    4. DeclarationVisitor - this provides CDecl instances, which provide information on declared variables
2. The topmost CStatement (a CProgram instance) can be _built_, i.e. transformed into an XCFA. This will recursively instantiate parts of the model until all statements are consumed.
3. The elements of the XCFA are passed through various _passes_, which will (among other modifications) remove empty edges, inline functions, and so on.
4. The XCFA is ready to be used.

To aid witness generation, there is an FrontendMetadata class which holds the following information:

#### cfaLoc:
- owner: XcfaLocation
- value: CFA.Loc

Stores the mapping from each XCFA location to their CFA counterpart. This is a 1:1 relation.

#### xcfaInterLoc:
- owner: XcfaEdge
- value: CFA.Loc
  
Stores the mapping from each XCFA edge to any number of CFA location which were necessary to achieve one Stmt per edge. This is a 1:N relation.

#### cfaEdge:
- owner: XcfaEdge
- value: CFA.Edge
  
Stores the mapping from each XCFA edge to CFA edges. This is a 1:N relation, N being the number of statements on the XCFA edge (or 1, if there is none).

#### sourceStatement:
- owner: XcfaEdge, XcfaLocation
- value: CStatement
  
Stores the source CStatement for every edge and location created by the Antlr-based C frontend. This is an N:1 relation.

#### lineNumberStart:
- owner: CStatement
- value: Integer 
  
Stores the starting line number of the CStatement.

#### lineNumberStop:
- owner: CStatement
- value: Integer
  
Stores the ending line number of the CStatement.

#### colNumberStart:
- owner: CStatement
- value: Integer
  
Stores the starting column number of the CStatement.

#### colNumberStop:
- owner: CStatement
- value: Integer
  
Stores the ending column number of the CStatement.

#### offsetStart:
- owner: CStatement
- value: Integer 
  
Stores the starting offset of the CStatement (inclusive).

#### offsetEnd:
- owner: CStatement
- value: Integer

Stores the ending offset of the CStatement (inclusive).

#### cSimpleType
- owner: Expr<?>
- value: CType

Stores the C type of the expression.

An example for retrieving starting line number information from a CFA.Edge:

``` java
private int retrieveStartLine(CFA.Edge edge) {
    Set<Object> xcfaEdges = FrontendMetadata.lookupMetadata("cfaEdge", edge);
    for (Object xcfaEdge : xcfaEdges) {
        Object sourceStatement = FrontendMetadata.lookupMetadata(xcfaEdge).get("sourceStatement");
        if(sourceStatement != null) {
            Object lineNumberStart = FrontendMetadata.lookupMetadata(sourceStatement).get("lineNumberStart");
            if(lineNumberStart instanceof Integer) {
                return (int) lineNumberStart;
            }
        }
    }
    return -1;
}
```