package hu.bme.mit.theta.frontend.c.parser.ast.visitor;

import hu.bme.mit.theta.frontend.c.parser.ast.FunctionDefinitionAst;
import hu.bme.mit.theta.frontend.c.parser.ast.VarDeclarationAst;

public interface DeclarationVisitor<D> {

	public D visit(VarDeclarationAst ast);

	public D visit(FunctionDefinitionAst ast);

}
