package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractParamRefExpr<DeclType extends Type> extends AbstractRefExpr<DeclType, ParamDecl<DeclType>>
		implements ParamRefExpr<DeclType> {

	public AbstractParamRefExpr(final ParamDecl<DeclType> paramDecl) {
		super(paramDecl);
	}

	@Override
	protected int getHashSeed() {
		return 919;
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}
}
