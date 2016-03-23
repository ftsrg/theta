package hu.bme.mit.inf.ttmc.code.ast;

import hu.bme.mit.inf.ttmc.code.ast.visitor.StatementVisitor;

abstract public class StatementAst extends AstNode {

	abstract public <S> S accept(StatementVisitor<S> visitor);
	
}
