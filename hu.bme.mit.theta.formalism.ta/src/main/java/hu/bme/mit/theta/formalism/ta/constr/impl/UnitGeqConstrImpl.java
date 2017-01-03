package hu.bme.mit.theta.formalism.ta.constr.impl;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;

import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.expr.ClockRefExpr;
import hu.bme.mit.theta.formalism.ta.utils.ClockConstrVisitor;

final class UnitGeqConstrImpl extends AbstractUnitConstr implements UnitGeqConstr {

	private static final int HASH_SEED = 2797;

	private static final String OPERATOR_LABEL = ">=";

	private volatile GeqExpr expr = null;

	UnitGeqConstrImpl(final ClockDecl clock, final int bound) {
		super(clock, bound);
	}

	@Override
	public GeqExpr toExpr() {
		GeqExpr result = expr;
		if (result == null) {
			final ClockRefExpr ref = getClock().getRef();
			result = Geq(ref, Int(getBound()));
			expr = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof UnitGeqConstr) {
			final UnitGeqConstr that = (UnitGeqConstr) obj;
			return this.getBound() == that.getBound() && this.getClock().equals(that.getClock());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
