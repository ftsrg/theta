package hu.bme.mit.inf.ttmc.code.ast.visitor;

import hu.bme.mit.inf.ttmc.code.ast.FunctionAst;
import hu.bme.mit.inf.ttmc.code.ast.VarDeclarationAst;

public interface DeclarationVisitor<D> {

	public D visit(VarDeclarationAst ast);
	public D visit(FunctionAst ast);
	
}
