package hu.bme.mit.theta.frontend.c.parser.ast.visitor;

import hu.bme.mit.theta.frontend.c.parser.ast.TranslationUnitAst;

public interface TranslationUnitVisitor<T> {

	public T visit(TranslationUnitAst ast);

}
