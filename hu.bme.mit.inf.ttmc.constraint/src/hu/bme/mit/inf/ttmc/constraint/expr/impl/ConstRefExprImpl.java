package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class ConstRefExprImpl<DeclType extends Type> extends AbstractConstRefExpr<DeclType> {

	public ConstRefExprImpl(ConstDecl<DeclType> constDecl) {
		super(constDecl);
	}

}
