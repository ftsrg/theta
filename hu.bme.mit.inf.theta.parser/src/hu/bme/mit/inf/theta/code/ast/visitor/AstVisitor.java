package hu.bme.mit.inf.theta.code.ast.visitor;

public interface AstVisitor<E, S, D, DR, T> extends ExpressionVisitor<E>, StatementVisitor<S>, DeclarationVisitor<D>, DeclaratorVisitor<DR>, TranslationUnitVisitor<T> {

	
	
}
