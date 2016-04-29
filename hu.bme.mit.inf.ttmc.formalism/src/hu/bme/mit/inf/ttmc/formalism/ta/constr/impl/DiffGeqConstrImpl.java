package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;

import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ConstrVisitor;

final class DiffGeqConstrImpl extends AbstractDiffConstr implements DiffGeqConstr {

	private static final int HASH_SEED = 4327;

	private static final String OPERATOR_LABEL = ">=";

	private volatile GeqExpr expr = null;

	DiffGeqConstrImpl(final Clock leftClock, final Clock rightClock, final int bound) {
		super(leftClock, rightClock, bound);
	}

	@Override
	public GeqExpr asExpr() {
		GeqExpr result = expr;
		if (result == null) {
			final ClockDecl leftDecl = getLeftClock().asDecl();
			final ClockDecl rightDecl = getRightClock().asDecl();
			result = Geq(Sub(Ref(leftDecl), Ref(rightDecl)), Int(getBound()));
			expr = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DiffGeqConstr) {
			final DiffGeqConstr that = (DiffGeqConstr) obj;
			return this.getBound() == that.getBound() && this.getLeftClock().equals(that.getLeftClock())
					&& this.getRightClock().equals(that.getRightClock());
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
