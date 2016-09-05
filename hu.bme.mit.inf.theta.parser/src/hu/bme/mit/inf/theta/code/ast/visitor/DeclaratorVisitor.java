package hu.bme.mit.inf.theta.code.ast.visitor;

import hu.bme.mit.inf.theta.code.ast.FunctionDeclaratorAst;
import hu.bme.mit.inf.theta.code.ast.InitDeclaratorAst;

public interface DeclaratorVisitor<DR> {

	public DR visit(InitDeclaratorAst ast);
	public DR visit(FunctionDeclaratorAst ast);
	
}
