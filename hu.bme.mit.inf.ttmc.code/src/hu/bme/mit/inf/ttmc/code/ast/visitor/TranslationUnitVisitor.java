package hu.bme.mit.inf.ttmc.code.ast.visitor;

import hu.bme.mit.inf.ttmc.code.ast.TranslationUnitAst;

public interface TranslationUnitVisitor<T> {

	public T visit(TranslationUnitAst ast);
	
}
