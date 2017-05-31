package hu.bme.mit.theta.formalism.xta;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.Type;

public final class ChanType implements Type {

	private static final ChanType INSTANCE = new ChanType();

	private ChanType() {
	}

	public static ChanType getInstance() {
		return INSTANCE;
	}

	@Override
	public String toString() {
		return "Chan";
	}

	////

	@Override
	public LitExpr<? extends Type> getAny() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
