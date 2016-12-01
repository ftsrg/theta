package hu.bme.mit.theta.frontend.c.parser.ast.visitor;

public interface AstVisitor<E, S, D, DR, T> extends ExpressionVisitor<E>, StatementVisitor<S>, DeclarationVisitor<D>,
		DeclaratorVisitor<DR>, TranslationUnitVisitor<T> {

}
