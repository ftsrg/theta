package hu.bme.mit.inf.theta.code.ast;

import hu.bme.mit.inf.theta.code.ast.visitor.StatementVisitor;

abstract public class StatementAst extends AstNode {

	abstract public <S> S accept(StatementVisitor<S> visitor);
	
	@Override
	abstract public StatementAst copy();
	
}
