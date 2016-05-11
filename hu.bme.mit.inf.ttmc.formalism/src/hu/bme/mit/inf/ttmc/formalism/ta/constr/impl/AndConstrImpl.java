package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static java.util.stream.Collectors.toSet;

import java.util.Collection;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.AndConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.AtomicConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.TrueConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ConstrVisitor;

final class AndConstrImpl implements AndConstr {

	private static final int HASH_SEED = 6133;

	private final Collection<? extends AtomicConstr> constrs;

	private volatile int hashCode = 0;
	private volatile AndExpr expr = null;

	AndConstrImpl(final Collection<? extends ClockConstr> constrs) {
		checkNotNull(constrs);
		this.constrs = toAtomicConstrs(constrs);
	}

	@Override
	public Collection<? extends AtomicConstr> getConstrs() {
		return constrs;
	}

	@Override
	public Collection<? extends ClockDecl> getClocks() {
		final ImmutableSet.Builder<ClockDecl> builder = ImmutableSet.builder();
		for (final ClockConstr constr : constrs) {
			builder.addAll(constr.getClocks());
		}
		return builder.build();
	}

	@Override
	public AndExpr asExpr() {
		AndExpr result = expr;
		if (result == null) {
			result = And(constrs.stream().map(ClockConstr::asExpr).collect(toSet()));
			expr = result;
		}
		return result;
	}

	@Override
	public <P, R> R accept(final ConstrVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + constrs.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AndConstr) {
			final AndConstr that = (AndConstr) obj;
			return this.getConstrs().equals(that.getConstrs());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "CC(", ")");
		constrs.forEach(c -> sj.add(c.toString()));
		return sj.toString();
	}

	////////

	private static Collection<AtomicConstr> toAtomicConstrs(final Collection<? extends ClockConstr> constrs) {
		final ImmutableSet.Builder<AtomicConstr> builder = ImmutableSet.builder();
		for (final ClockConstr constr : constrs) {
			if (constr instanceof AtomicConstr) {
				builder.add((AtomicConstr) constr);
			} else if (constr instanceof AndConstr) {
				builder.addAll(((AndConstr) constr).getConstrs());
			} else if (constr instanceof TrueConstr) {
				continue;
			} else {
				throw new AssertionError();
			}
		}
		return builder.build();
	}

}
