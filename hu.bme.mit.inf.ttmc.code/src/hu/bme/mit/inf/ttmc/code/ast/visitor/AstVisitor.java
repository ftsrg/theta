package hu.bme.mit.inf.ttmc.code.ast.visitor;

public interface AstVisitor<E, S, D, DR> extends ExpressionVisitor<E>, StatementVisitor<S>, DeclarationVisitor<D>, DeclaratorVisitor<DR> {

	
	
}
