package hu.bme.mit.inf.ttmc.code.ast.visitor;

public interface AstVisitor<E, S> extends ExpressionVisitor<E>, StatementVisitor<S> {

	
	
}
