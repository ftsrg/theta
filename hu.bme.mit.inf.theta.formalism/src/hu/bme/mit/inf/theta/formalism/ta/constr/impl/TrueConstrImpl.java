package hu.bme.mit.inf.theta.formalism.ta.constr.impl;

import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.True;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.theta.core.expr.TrueExpr;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.ta.constr.TrueConstr;
import hu.bme.mit.inf.theta.formalism.ta.utils.ClockConstrVisitor;

final class TrueConstrImpl implements TrueConstr {

	private static final int HASH_SEED = 2014099;

	private static final String CC_LABEL = "CC(true)";

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		return ImmutableSet.of();
	}

	@Override
	public TrueExpr toExpr() {
		return True();
	}

	@Override
	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof TrueConstr;
	}

	@Override
	public String toString() {
		return CC_LABEL;
	}
}
