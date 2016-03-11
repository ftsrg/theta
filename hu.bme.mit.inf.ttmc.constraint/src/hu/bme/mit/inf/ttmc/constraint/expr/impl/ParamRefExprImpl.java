package hu.bme.mit.inf.ttmc.constraint.expr.impl;


import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class ParamRefExprImpl<DeclType extends Type> extends AbstractRefExpr<DeclType, ParamDecl<DeclType>> implements ParamRefExpr<DeclType> {

	public ParamRefExprImpl(final ParamDecl<DeclType> paramDecl) {
		super(paramDecl);
	}

	@Override
	protected int getHashSeed() {
		return 919;
	}
	
	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
