package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstrs;

final class DiffBounds {

	private static final int INF = Integer.MAX_VALUE;

	private static final String INF_STRING = "inf";

	public static int Inf() {
		return INF;
	}

	public static int Bound(final int m, final boolean strict) {
		return strict ? Lt(m) : Leq(m);
	}

	public static int Lt(final int m) {
		return m << 1;
	}

	public static int Leq(final int m) {
		return (m << 1) | 1;
	}

	////

	public static ClockConstr toConstr(final VarDecl<RatType> leftVar, final VarDecl<RatType> rightVar,
			final int b) {
		checkNotNull(leftVar);
		checkNotNull(rightVar);

		if (b == Inf()) {
			return ClockConstrs.True();
		}

		if (leftVar.equals(rightVar)) {
			if (b < Leq(0)) {
				return ClockConstrs.False();
			} else {
				return ClockConstrs.True();
			}
		}

		final int bound = getBound(b);
		final boolean strict = isStrict(b);

		if (leftVar.equals(ZeroVar.getInstance())) {
			if (rightVar.equals(ZeroVar.getInstance())) {
				throw new AssertionError();
			} else {
				if (strict) {
					return ClockConstrs.Gt(rightVar, -bound);
				} else {
					return ClockConstrs.Geq(rightVar, -bound);
				}
			}
		} else {
			if (rightVar.equals(ZeroVar.getInstance())) {
				if (strict) {
					return ClockConstrs.Lt(leftVar, bound);
				} else {
					return ClockConstrs.Leq(leftVar, bound);
				}
			} else {
				if (strict) {
					return ClockConstrs.Lt(leftVar, rightVar, bound);
				} else {
					return ClockConstrs.Leq(leftVar, rightVar, bound);
				}
			}
		}

	}

	////

	public static int add(final int b1, final int b2) {
		return (b1 == INF || b2 == INF) ? INF : b1 + b2 - ((b1 & 1) | (b2 & 1));
	}

	public static int negate(final int b) {
		checkArgument(b != INF, "Bound is INF");
		return Bound(-getBound(b), !isStrict(b));
	}

	////

	public static int getBound(final int b) {
		return b >> 1;
	}

	public static boolean isStrict(final int b) {
		return (b & 1) == 0;
	}

	public static String asString(final int b) {
		if (b == INF) {
			return INF_STRING;
		} else {
			return finiteBoundAsString(b);
		}
	}

	private static String finiteBoundAsString(final int b) {
		assert b != INF;

		final StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(getBound(b));
		sb.append(", ");
		if (isStrict(b)) {
			sb.append("<");
		} else {
			sb.append("<=");
		}
		sb.append(")");
		return sb.toString();
	}

}
