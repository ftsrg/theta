package hu.bme.mit.inf.ttmc.code.ast.visitor;

public interface AstVisitor<E, S, D> extends ExpressionVisitor<E>, StatementVisitor<S>, DeclarationVisitor<D> {

	
	
}
