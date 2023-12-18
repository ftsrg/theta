/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.core.clock.constr;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.clocktype.ClockExprs.Clock;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.clocktype.*;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.*;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class ClockConstrs {

	private static final TrueConstr TRUE_CONSTR;
	private static final FalseConstr FALSE_CONSTR;

	static {
		TRUE_CONSTR = new TrueConstr();
		FALSE_CONSTR = new FalseConstr();
	}

	private ClockConstrs() {
	}

	////

	public static ClockConstr fromExpr(final Expr<BoolType> expr) {
		return FromExprHelper.INSTANCE.transform(expr);
	}

	public static ClockConstr fromClockExpr(final ClockConstraintExpr expr) {
		return FromClockExprHelper.INSTANCE.transform(expr);
	}

	////

	public static TrueConstr True() {
		return TRUE_CONSTR;
	}

	public static FalseConstr False() {
		return FALSE_CONSTR;
	}

	public static UnitLtConstr Lt(final VarDecl<ClockType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitLtConstr(clock, bound);
	}

	public static UnitLeqConstr Leq(final VarDecl<ClockType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitLeqConstr(clock, bound);
	}

	public static UnitGtConstr Gt(final VarDecl<ClockType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitGtConstr(clock, bound);
	}

	public static UnitGeqConstr Geq(final VarDecl<ClockType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitGeqConstr(clock, bound);
	}

	public static UnitEqConstr Eq(final VarDecl<ClockType> clock, final int bound) {
		checkNotNull(clock);
		return new UnitEqConstr(clock, bound);
	}

	public static DiffLtConstr Lt(final VarDecl<ClockType> leftClock, final VarDecl<ClockType> rightClock,
								  final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLtConstr(leftClock, rightClock, bound);
	}

	public static DiffLeqConstr Leq(final VarDecl<ClockType> leftClock, final VarDecl<ClockType> rightClock,
									final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLeqConstr(leftClock, rightClock, bound);
	}

	public static DiffGtConstr Gt(final VarDecl<ClockType> leftClock, final VarDecl<ClockType> rightClock,
								  final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGtConstr(leftClock, rightClock, bound);
	}

	public static DiffGeqConstr Geq(final VarDecl<ClockType> leftClock, final VarDecl<ClockType> rightClock,
									final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGeqConstr(leftClock, rightClock, bound);
	}

	public static DiffEqConstr Eq(final VarDecl<ClockType> leftClock, final VarDecl<ClockType> rightClock,
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

	private static final class FromExprHelper {

		private static final FromExprHelper INSTANCE = new FromExprHelper();

		private final DispatchTable<ClockConstr> table;

		private FromExprHelper() {
			table = DispatchTable.<ClockConstr>builder()

					.addCase(TrueExpr.class, this::transformTrue)

					.addCase(FalseExpr.class, this::transformFalse)

					.addCase(RatLtExpr.class, this::transformLt)

					.addCase(RatLeqExpr.class, this::transformLeq)

					.addCase(RatGtExpr.class, this::transformGt)

					.addCase(RatGeqExpr.class, this::transformGeq)

					.addCase(RatEqExpr.class, this::transformEq)

					.addCase(AndExpr.class, this::transformAnd)

					.addDefault(o -> {
						throw new IllegalArgumentException();
					})

					.build();
		}

		public ClockConstr transform(final Expr<BoolType> expr) {
			return table.dispatch(expr);
		}

		private TrueConstr transformTrue(final TrueExpr expr) {
			return True();
		}

		private FalseConstr transformFalse(final FalseExpr expr) {
			return False();
		}

		private ClockConstr transformLt(final RatLtExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Lt(lhs.get(0), rhs);
			} else {
				return Lt(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformLeq(final RatLeqExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Leq(lhs.get(0), rhs);
			} else {
				return Leq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformGt(final RatGtExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Gt(lhs.get(0), rhs);
			} else {
				return Gt(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformGeq(final RatGeqExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Geq(lhs.get(0), rhs);
			} else {
				return Geq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformEq(final RatEqExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractConstrLhs(expr);
			final int rhs = extractConstrRhs(expr);
			if (lhs.size() == 1) {
				return Eq(lhs.get(0), rhs);
			} else {
				return Eq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private AndConstr transformAnd(final AndExpr expr) {
			final ImmutableSet.Builder<ClockConstr> builder = ImmutableSet.builder();
			for (final Expr<BoolType> op : expr.getOps()) {
				builder.add(transform(op));
			}
			return And(builder.build());
		}

		private static List<VarDecl<ClockType>> extractConstrLhs(final BinaryExpr<RatType, BoolType> expr) {
			final Expr<?> leftOp = expr.getLeftOp();

			if (leftOp instanceof RefExpr) {
				final RefExpr<?> leftRef = (RefExpr<?>) leftOp;
				final Decl<?> leftDecl = leftRef.getDecl();
				if (leftDecl instanceof VarDecl) {
					final VarDecl<?> leftVar = (VarDecl<?>) leftDecl;
					final VarDecl<ClockType> leftRatVar = TypeUtils.cast(leftVar, Clock());
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
						final VarDecl<ClockType> subLeftRatVar = TypeUtils.cast(subLeftVar, Clock());
						final VarDecl<ClockType> subRightRatVar = TypeUtils.cast(subRightVar, Clock());
						return ImmutableList.of(subLeftRatVar, subRightRatVar);
					}
				}
			}

			throw new IllegalArgumentException();
		}

		private static int extractConstrRhs(final BinaryExpr<?, BoolType> expr) {
			final Expr<?> rightOp = ExprUtils.simplify(expr.getRightOp());

			if (rightOp instanceof RatLitExpr) {
				final RatLitExpr ratLit = (RatLitExpr) rightOp;
				if (ratLit.getDenom().intValue() == 1) {
					final int num = ratLit.getNum().intValue();
					return num;
				}
			}

			throw new IllegalArgumentException();
		}

	}

	private static final class FromClockExprHelper {

		private static final FromClockExprHelper INSTANCE = new FromClockExprHelper();

		private final DispatchTable<ClockConstr> table;

		private FromClockExprHelper() {
			table = DispatchTable.<ClockConstr>builder()

					.addCase(ClockLtExpr.class, this::transformLt)

					.addCase(ClockLeqExpr.class, this::transformLeq)

					.addCase(ClockGtExpr.class, this::transformGt)

					.addCase(ClockGeqExpr.class, this::transformGeq)

					.addCase(ClockEqExpr.class, this::transformEq)

					.addDefault(o -> {
						throw new IllegalArgumentException();
					})

					.build();
		}

		public ClockConstr transform(final Expr<BoolType> expr) {
			return table.dispatch(expr);
		}

		private ClockConstr transformLt(final ClockLtExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractClocks(expr.getLeftOp());
			final int rhs = extractValue(expr.getRightOp());
			if (lhs.size() == 1) {
				return Lt(lhs.get(0), rhs);
			} else {
				return Lt(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformLeq(final ClockLeqExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractClocks(expr.getLeftOp());
			final int rhs = extractValue(expr.getRightOp());
			if (lhs.size() == 1) {
				return Leq(lhs.get(0), rhs);
			} else {
				return Leq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformGt(final ClockGtExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractClocks(expr.getLeftOp());
			final int rhs = extractValue(expr.getRightOp());
			if (lhs.size() == 1) {
				return Gt(lhs.get(0), rhs);
			} else {
				return Gt(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformGeq(final ClockGeqExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractClocks(expr.getLeftOp());
			final int rhs = extractValue(expr.getRightOp());
			if (lhs.size() == 1) {
				return Geq(lhs.get(0), rhs);
			} else {
				return Geq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private ClockConstr transformEq(final ClockEqExpr expr) {
			final List<VarDecl<ClockType>> lhs = extractClocks(expr.getLeftOp());
			final int rhs = extractValue(expr.getRightOp());
			if (lhs.size() == 1) {
				return Eq(lhs.get(0), rhs);
			} else {
				return Eq(lhs.get(0), lhs.get(1), rhs);
			}
		}

		private static List<VarDecl<ClockType>> extractClocks(final Expr<ClockType> expr) {

			if (expr instanceof RefExpr) {
				final RefExpr<ClockType> clockRefExpr = (RefExpr<ClockType>) expr;
				final Decl<ClockType> clockDecl = clockRefExpr.getDecl();
				if (clockDecl instanceof VarDecl) {
					final VarDecl<ClockType> clockVar = (VarDecl<ClockType>) clockDecl;
					return ImmutableList.of(clockVar);
				}
			}

			if (expr instanceof ClockDiffExpr) {
				final ClockDiffExpr clockDiffExpr = (ClockDiffExpr) expr;
				final Expr<ClockType> leftClockExpr = clockDiffExpr.getLeftOp();
				final Expr<ClockType> rightClockExpr = clockDiffExpr.getRightOp();
				if (leftClockExpr instanceof RefExpr && rightClockExpr instanceof RefExpr) {
					final Decl<ClockType> leftClockDecl = ((RefExpr<ClockType>) leftClockExpr).getDecl();
					final Decl<ClockType> rightClockDecl = ((RefExpr<ClockType>) rightClockExpr).getDecl();
					if (leftClockDecl instanceof VarDecl && rightClockDecl instanceof VarDecl) {
						final VarDecl<ClockType> leftClockVar = (VarDecl<ClockType>) leftClockDecl;
						final VarDecl<ClockType> rightClockVar = (VarDecl<ClockType>) rightClockDecl;
						return ImmutableList.of(leftClockVar, rightClockVar);
					}
				}
			}

			throw new IllegalArgumentException();
		}

		private static int extractValue(final Expr<IntType> expr) {
			final Expr<IntType> simplifiedExpr = ExprUtils.simplify(expr);

			if (simplifiedExpr instanceof IntLitExpr) {
				final IntLitExpr intLitExpr = (IntLitExpr) simplifiedExpr;
				return intLitExpr.getValue().intValueExact();
			}

			throw new IllegalArgumentException();
		}
	}

}
