package hu.bme.mit.inf.theta.code.ast.visitor;

import hu.bme.mit.inf.theta.code.ast.FunctionDefinitionAst;
import hu.bme.mit.inf.theta.code.ast.VarDeclarationAst;

public interface DeclarationVisitor<D> {

	public D visit(VarDeclarationAst ast);
	public D visit(FunctionDefinitionAst ast);
	
}
