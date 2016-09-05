package hu.bme.mit.inf.theta.code.ast.visitor;

import hu.bme.mit.inf.theta.code.ast.TranslationUnitAst;

public interface TranslationUnitVisitor<T> {

	public T visit(TranslationUnitAst ast);
	
}
