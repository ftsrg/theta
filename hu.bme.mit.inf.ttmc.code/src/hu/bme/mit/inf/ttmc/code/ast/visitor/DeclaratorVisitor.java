package hu.bme.mit.inf.ttmc.code.ast.visitor;

import hu.bme.mit.inf.ttmc.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.ttmc.code.ast.InitDeclaratorAst;

public interface DeclaratorVisitor<DR> {

	public DR visit(InitDeclaratorAst ast);
	public DR visit(FunctionDeclaratorAst ast);
	
}
