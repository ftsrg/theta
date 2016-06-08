package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.utils.impl.FailExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.AndConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.EqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.GeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.GtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.LeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.LtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.TrueConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLtConstr;

public final class ClockConstrs {

	private static final ExprToClockConstrVisitor VISITOR;

	private static final TrueConstr TRUE_CONSTR;

	static {
		VISITOR = new ExprToClockConstrVisitor();
		TRUE_CONSTR = new TrueConstrImpl();
	}

	private ClockConstrs() {
	}

	////

	public static ClockConstr formExpr(final Expr<? extends BoolType> expr) {
		return expr.accept(VISITOR, null);
	}

	////

	public static TrueConstr True() {
		return TRUE_CONSTR;
	}

	public static UnitLtConstr Lt(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitLtConstrImpl(clock, bound);
	}

	public static UnitLeqConstr Leq(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitLeqConstrImpl(clock, bound);
	}

	public static UnitGtConstr Gt(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitGtConstrImpl(clock, bound);
	}

	public static UnitGeqConstr Geq(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitGeqConstrImpl(clock, bound);
	}

	public static UnitEqConstr Eq(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitEqConstrImpl(clock, bound);
	}

	public static DiffLtConstr Lt(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLtConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffLeqConstr Leq(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLeqConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffGtConstr Gt(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGtConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffGeqConstr Geq(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGeqConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffEqConstr Eq(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffEqConstrImpl(leftClock, rightClock, bound);
	}

	public static AndConstr And(final Collection<? extends ClockConstr> constrs) {
		checkNotNull(constrs);
		return new AndConstrImpl(constrs);
	}

	////

	public static AndConstr And(final ClockConstr... constrs) {
		checkNotNull(constrs);
		return And(ImmutableSet.copyOf(constrs));
	}

	////

	private static final class ExprToClockConstrVisitor extends FailExprVisitor<Void, ClockConstr> {

		private ExprToClockConstrVisitor() {
		}

		@Override
		public TrueConstr visit(final TrueExpr expr, final Void param) {
			return True();
		}

		@Override
		public LtConstr visit(final LtExpr expr, final Void param) {
			final ClockDecl[] lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.length == 1) {
				return Lt(lhs[0], rhs);
			} else {
				return Lt(lhs[0], lhs[1], rhs);
			}
		}

		@Override
		public LeqConstr visit(final LeqExpr expr, final Void param) {
			final ClockDecl[] lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.length == 1) {
				return Leq(lhs[0], rhs);
			} else {
				return Leq(lhs[0], lhs[1], rhs);
			}
		}

		@Override
		public GtConstr visit(final GtExpr expr, final Void param) {
			final ClockDecl[] lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.length == 1) {
				return Gt(lhs[0], rhs);
			} else {
				return Gt(lhs[0], lhs[1], rhs);
			}
		}

		@Override
		public GeqConstr visit(final GeqExpr expr, final Void param) {
			final ClockDecl[] lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.length == 1) {
				return Geq(lhs[0], rhs);
			} else {
				return Geq(lhs[0], lhs[1], rhs);
			}
		}

		@Override
		public EqConstr visit(final EqExpr expr, final Void param) {
			final ClockDecl[] lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.length == 1) {
				return Eq(lhs[0], rhs);
			} else {
				return Eq(lhs[0], lhs[1], rhs);
			}
		}

		@Override
		public AndConstr visit(final AndExpr expr, final Void param) {
			final ImmutableSet.Builder<ClockConstr> builder = ImmutableSet.builder();
			for (final Expr<? extends BoolType> op : expr.getOps()) {
				builder.add(op.accept(this, param));
			}
			return And(builder.build());
		}

		private ClockDecl[] extractConstrLhs(final BinaryExpr<?, ?, BoolType> expr) {
			final Expr<?> leftOp = expr.getLeftOp();

			if (leftOp instanceof ClockRefExpr) {
				final ClockDecl clock = ((ClockRefExpr) leftOp).getDecl();
				return new ClockDecl[] { clock };
			}

			if (leftOp instanceof SubExpr) {
				final SubExpr<?> subExpr = (SubExpr<?>) leftOp;
				final Expr<?> subLeftOp = subExpr.getLeftOp();
				final Expr<?> subRightOp = subExpr.getRightOp();
				if (subLeftOp instanceof ClockRefExpr && subRightOp instanceof ClockRefExpr) {
					final ClockDecl leftClock = ((ClockRefExpr) subLeftOp).getDecl();
					final ClockDecl rightClock = ((ClockRefExpr) subRightOp).getDecl();
					return new ClockDecl[] { leftClock, rightClock };
				}
			}

			throw new IllegalArgumentException();
		}

		private int extractConstrRhs(final BinaryExpr<?, ?, BoolType> expr) {
			final Expr<?> rightOp = expr.getLeftOp();

			if (rightOp instanceof IntLitExpr) {
				final IntLitExpr intLitExpr = (IntLitExpr) rightOp;
				final long value = intLitExpr.getValue();
				return Math.toIntExact(value);
			}

			throw new IllegalArgumentException();
		}

	}

}
