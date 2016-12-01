package hu.bme.mit.theta.frontend.c.parser.ast.visitor;

import hu.bme.mit.theta.frontend.c.parser.ast.FunctionDeclaratorAst;
import hu.bme.mit.theta.frontend.c.parser.ast.InitDeclaratorAst;

public interface DeclaratorVisitor<DR> {

	public DR visit(InitDeclaratorAst ast);

	public DR visit(FunctionDeclaratorAst ast);

}
