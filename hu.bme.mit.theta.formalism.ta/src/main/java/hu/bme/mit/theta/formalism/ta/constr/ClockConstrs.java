package hu.bme.mit.theta.formalism.ta.constr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.impl.Types.Rat;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
import hu.bme.mit.theta.core.utils.impl.FailExprVisitor;
import hu.bme.mit.theta.core.utils.impl.TypeUtils;

public final class ClockConstrs {

	private static final ExprToClockConstrVisitor VISITOR;

	private static final TrueConstr TRUE_CONSTR;
	private static final FalseConstr FALSE_CONSTR;

	static {
		VISITOR = new ExprToClockConstrVisitor();
		TRUE_CONSTR = new TrueConstr();
		FALSE_CONSTR = new FalseConstr();
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

	public static FalseConstr False() {
		return FALSE_CONSTR;
	}

	public static UnitLtConstr Lt(final VarDecl<RatType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitLtConstr(clock, bound);
	}

	public static UnitLeqConstr Leq(final VarDecl<RatType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitLeqConstr(clock, bound);
	}

	public static UnitGtConstr Gt(final VarDecl<RatType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitGtConstr(clock, bound);
	}

	public static UnitGeqConstr Geq(final VarDecl<RatType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitGeqConstr(clock, bound);
	}

	public static UnitEqConstr Eq(final VarDecl<RatType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitEqConstr(clock, bound);
	}

	public static DiffLtConstr Lt(final VarDecl<RatType> leftClock, final VarDecl<RatType> rightClock,
			final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLtConstr(leftClock, rightClock, bound);
	}

	public static DiffLeqConstr Leq(final VarDecl<RatType> leftClock, final VarDecl<RatType> rightClock,
			final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLeqConstr(leftClock, rightClock, bound);
	}

	public static DiffGtConstr Gt(final VarDecl<RatType> leftClock, final VarDecl<RatType> rightClock,
			final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGtConstr(leftClock, rightClock, bound);
	}

	public static DiffGeqConstr Geq(final VarDecl<RatType> leftClock, final VarDecl<RatType> rightClock,
			final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGeqConstr(leftClock, rightClock, bound);
	}

	public static DiffEqConstr Eq(final VarDecl<RatType> leftClock, final VarDecl<RatType> rightClock,
			final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffEqConstr(leftClock, rightClock, bound);
	}

	public static AndConstr And(final Collection<? extends ClockConstr> constrs) {
		checkNotNull(constrs);
		return new AndConstr(constrs);
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
		public FalseConstr visit(final FalseExpr expr, final Void param) {
			return False();
		}

		@Override
		public ClockConstr visit(final LtExpr expr, final Void param) {
			final List<VarDecl<RatType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Lt(lhs.get(0), rhs);
			} else {
				return Lt(lhs.get(0), lhs.get(1), rhs);
			}
		}

		@Override
		public ClockConstr visit(final LeqExpr expr, final Void param) {
			final List<VarDecl<RatType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Leq(lhs.get(0), rhs);
			} else {
				return Leq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		@Override
		public ClockConstr visit(final GtExpr expr, final Void param) {
			final List<VarDecl<RatType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Gt(lhs.get(0), rhs);
			} else {
				return Gt(lhs.get(0), lhs.get(1), rhs);
			}
		}

		@Override
		public ClockConstr visit(final GeqExpr expr, final Void param) {
			final List<VarDecl<RatType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Geq(lhs.get(0), rhs);
			} else {
				return Geq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		@Override
		public ClockConstr visit(final EqExpr expr, final Void param) {
			final List<VarDecl<RatType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Eq(lhs.get(0), rhs);
			} else {
				return Eq(lhs.get(0), lhs.get(1), rhs);
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

		private List<VarDecl<RatType>> extractConstrLhs(final BinaryExpr<?, ?, BoolType> expr) {
			final Expr<?> leftOp = expr.getLeftOp();

			if (leftOp instanceof RefExpr) {
				final RefExpr<?> leftRef = (RefExpr<?>) leftOp;
				final Decl<?> leftDecl = leftRef.getDecl();
				if (leftDecl instanceof VarDecl) {
					final VarDecl<?> leftVar = (VarDecl<?>) leftDecl;
					final VarDecl<RatType> leftRatVar = TypeUtils.cast(leftVar, Rat());
					return ImmutableList.of(leftRatVar);
				}
			}

			if (leftOp instanceof RatSubExpr) {
				final RatSubExpr subExpr = (RatSubExpr) leftOp;
				// TODO
				final Expr<?> subLeftOp = subExpr.getLeftOp();
				final Expr<?> subRightOp = subExpr.getRightOp();
				if (subLeftOp instanceof RefExpr && subRightOp instanceof RefExpr) {
					final RefExpr<?> subLeftRef = (RefExpr<?>) subLeftOp;
					final RefExpr<?> subRightRef = (RefExpr<?>) subRightOp;
					final Decl<?> subLeftDecl = subLeftRef.getDecl();
					final Decl<?> subRightDecl = subRightRef.getDecl();
					if (subLeftDecl instanceof VarDecl && subRightDecl instanceof VarDecl) {
						final VarDecl<?> subLeftVar = (VarDecl<?>) subLeftDecl;
						final VarDecl<?> subRightVar = (VarDecl<?>) subRightDecl;
						final VarDecl<RatType> subLeftRatVar = TypeUtils.cast(subLeftVar, Rat());
						final VarDecl<RatType> subRightRatVar = TypeUtils.cast(subRightVar, Rat());
						return ImmutableList.of(subLeftRatVar, subRightRatVar);
					}
				}
			}

			throw new IllegalArgumentException();
		}

		private int extractConstrRhs(final BinaryExpr<?, ?, BoolType> expr) {
			final Expr<?> rightOp = expr.getRightOp();

			if (rightOp instanceof IntLitExpr) {
				final IntLitExpr intLitExpr = (IntLitExpr) rightOp;
				final long value = intLitExpr.getValue();
				return Math.toIntExact(value);
			}

			throw new IllegalArgumentException();
		}

	}

}
