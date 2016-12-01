package hu.bme.mit.theta.frontend.c.parser.ast;

import hu.bme.mit.theta.frontend.c.parser.ast.visitor.StatementVisitor;

abstract public class StatementAst extends AstNode {

	abstract public <S> S accept(StatementVisitor<S> visitor);

	@Override
	abstract public StatementAst copy();

}
