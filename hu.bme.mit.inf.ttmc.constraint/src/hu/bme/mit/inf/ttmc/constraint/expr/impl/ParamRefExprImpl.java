package hu.bme.mit.inf.ttmc.constraint.expr.impl;


import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ParamRefExprImpl<DeclType extends Type> extends AbstractRefExpr<DeclType, ParamDecl<DeclType>> implements ParamRefExpr<DeclType> {

	public ParamRefExprImpl(final ParamDecl<DeclType> paramDecl) {
		super(paramDecl);
	}

	@Override
	protected int getHashSeed() {
		return 919;
	}

}
