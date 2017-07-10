package hu.bme.mit.theta.core.utils;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.inttype.ModExpr;
import hu.bme.mit.theta.core.type.rattype.RatAddExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatEqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGtExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;
import hu.bme.mit.theta.core.type.rattype.RatMulExpr;
import hu.bme.mit.theta.core.type.rattype.RatNegExpr;
import hu.bme.mit.theta.core.type.rattype.RatNeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class ExprSimplifier {

	private final DispatchTable<Expr<?>> table;
	private final Valuation val;

	ExprSimplifier(final Valuation val) {
		this.val = checkNotNull(val);

		table = DispatchTable.<Expr<?>>builder()

				// Boolean

				.addCase(NotExpr.class, this::simplifyNot)

				.addCase(ImplyExpr.class, this::simplifyImply)

				.addCase(IffExpr.class, this::simplifyIff)

				.addCase(AndExpr.class, this::simplifyAnd)

				.addCase(OrExpr.class, this::simplifyOr)

				// Rational

				.addCase(RatAddExpr.class, this::simplifyRatAdd)

				.addCase(RatSubExpr.class, this::simplifyRatSub)

				.addCase(RatNegExpr.class, this::simplifyRatNeg)

				.addCase(RatMulExpr.class, this::simplifyRatMul)

				.addCase(RatDivExpr.class, this::simplifyRatDiv)

				.addCase(RatEqExpr.class, this::simplifyRatEq)

				.addCase(RatNeqExpr.class, this::simplifyRatNeq)

				.addCase(RatGeqExpr.class, this::simplifyRatGeq)

				.addCase(RatGtExpr.class, this::simplifyRatGt)

				.addCase(RatLeqExpr.class, this::simplifyRatLeq)

				.addCase(RatLtExpr.class, this::simplifyRatLt)

				// Integer

				.addCase(IntToRatExpr.class, this::simplifyIntToRat)

				.addCase(IntAddExpr.class, this::simplifyIntAdd)

				.addCase(IntSubExpr.class, this::simplifyIntSub)

				.addCase(IntNegExpr.class, this::simplifyIntNeg)

				.addCase(IntMulExpr.class, this::simplifyIntMul)

				.addCase(IntDivExpr.class, this::simplifyIntDiv)

				.addCase(ModExpr.class, this::simplifyMod)

				.addCase(IntEqExpr.class, this::simplifyIntEq)

				.addCase(IntNeqExpr.class, this::simplifyIntNeq)

				.addCase(IntGeqExpr.class, this::simplifyIntGeq)

				.addCase(IntGtExpr.class, this::simplifyIntGt)

				.addCase(IntLeqExpr.class, this::simplifyIntLeq)

				.addCase(IntLtExpr.class, this::simplifyIntLt)

				// General

				.addCase(RefExpr.class, this::simplifyRef)

				.addCase(IteExpr.class, this::simplifyIte)

				// Default

				.addDefault(o -> {
					final Expr<?> expr = (Expr<?>) o;
					return expr.map(this::simplify);
				})

				.build();
	}

	@SuppressWarnings("unchecked")
	public <T extends Type> Expr<T> simplify(final Expr<T> expr) {
		return (Expr<T>) table.dispatch(expr);
	}

	/*
	 * General
	 */

	private Expr<?> simplifyRef(final RefExpr<?> expr) {
		return simplifyGenericRef(expr);
	}

	// TODO Eliminate helper method once the Java compiler is able to handle
	// this kind of type inference
	private <DeclType extends Type> Expr<DeclType> simplifyGenericRef(final RefExpr<DeclType> expr) {
		final Optional<LitExpr<DeclType>> eval = val.eval(expr.getDecl());
		if (eval.isPresent()) {
			return eval.get();
		}

		return expr;
	}

	private Expr<?> simplifyIte(final IteExpr<?> expr) {
		return simplifyGenericIte(expr);
	}

	// TODO Eliminate helper method once the Java compiler is able to handle
	// this kind of type inference
	private <ExprType extends Type> Expr<ExprType> simplifyGenericIte(final IteExpr<ExprType> expr) {
		final Expr<BoolType> cond = simplify(expr.getCond());

		if (cond instanceof TrueExpr) {
			final Expr<ExprType> then = simplify(expr.getThen());
			return then;

		} else if (cond instanceof FalseExpr) {
			final Expr<ExprType> elze = simplify(expr.getElse());
			return elze;
		}

		final Expr<ExprType> then = simplify(expr.getThen());
		final Expr<ExprType> elze = simplify(expr.getElse());

		return expr.with(cond, then, elze);
	}

	/*
	 * Booleans
	 */

	private Expr<BoolType> simplifyNot(final NotExpr expr) {
		final Expr<BoolType> op = simplify(expr.getOp());
		if (op instanceof NotExpr) {
			return ((NotExpr) op).getOp();
		} else if (op instanceof TrueExpr) {
			return False();
		} else if (op instanceof FalseExpr) {
			return True();
		}

		return expr.with(op);
	}

	private Expr<BoolType> simplifyImply(final ImplyExpr expr) {
		final Expr<BoolType> leftOp = simplify(expr.getLeftOp());
		final Expr<BoolType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof BoolLitExpr && rightOp instanceof BoolLitExpr) {
			final boolean leftValue = ((BoolLitExpr) leftOp).getValue();
			final boolean rightValue = ((BoolLitExpr) rightOp).getValue();
			return Bool(!leftValue || rightValue);
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		if (leftOp instanceof FalseExpr || rightOp instanceof TrueExpr) {
			return True();
		} else if (leftOp instanceof TrueExpr) {
			return rightOp;
		} else if (rightOp instanceof FalseExpr) {
			return simplify(Not(leftOp));
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyIff(final IffExpr expr) {
		final Expr<BoolType> leftOp = simplify(expr.getLeftOp());
		final Expr<BoolType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof BoolLitExpr && rightOp instanceof BoolLitExpr) {
			final boolean leftValue = ((BoolLitExpr) leftOp).getValue();
			final boolean rightValue = ((BoolLitExpr) rightOp).getValue();
			return Bool(leftValue == rightValue);
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		if (leftOp instanceof TrueExpr) {
			return rightOp;
		} else if (rightOp instanceof TrueExpr) {
			return leftOp;
		} else if (leftOp instanceof FalseExpr) {
			return simplify(Not(rightOp));
		} else if (rightOp instanceof FalseExpr) {
			return simplify(Not(leftOp));
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyAnd(final AndExpr expr) {
		final List<Expr<BoolType>> ops = new ArrayList<>();

		if (expr.getOps().size() == 0)
			return True();

		for (final Expr<BoolType> op : expr.getOps()) {
			final Expr<BoolType> opVisited = simplify(op);
			if (opVisited instanceof TrueExpr) {
				continue;
			} else if (opVisited instanceof FalseExpr) {
				return False();
			} else if (opVisited instanceof AndExpr) {
				final AndExpr andOp = (AndExpr) opVisited;
				ops.addAll(andOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		if (ops.size() == 0) {
			return True();
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private Expr<BoolType> simplifyOr(final OrExpr expr) {
		final List<Expr<BoolType>> ops = new ArrayList<>();

		if (expr.getOps().size() == 0)
			return True();

		for (final Expr<BoolType> op : expr.getOps()) {
			final Expr<BoolType> opVisited = simplify(op);
			if (opVisited instanceof FalseExpr) {
				continue;
			} else if (opVisited instanceof TrueExpr) {
				return True();
			} else if (opVisited instanceof OrExpr) {
				final OrExpr orOp = (OrExpr) opVisited;
				ops.addAll(orOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		if (ops.size() == 0) {
			return False();
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	/*
	 * Rationals
	 */

	private Expr<RatType> simplifyRatAdd(final RatAddExpr expr) {
		final List<Expr<RatType>> ops = new ArrayList<>();
		int num = 0;
		int denom = 1;

		for (final Expr<RatType> op : expr.getOps()) {
			final Expr<RatType> opVisited = simplify(op);
			if (opVisited instanceof RatLitExpr) {
				final RatLitExpr litOp = (RatLitExpr) opVisited;
				num = num * litOp.getDenom() + denom * litOp.getNum();
				denom *= litOp.getDenom();
			} else if (opVisited instanceof RatAddExpr) {
				final RatAddExpr addOp = (RatAddExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		final Expr<RatType> sum = Rat(num, denom);

		if (!sum.equals(Rat(0, 1))) {
			ops.add(sum);
		}

		if (ops.size() == 0) {
			return Rat(0, 1);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private Expr<RatType> simplifyRatSub(final RatSubExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return leftLit.sub(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return Rat(0, 1);
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<RatType> simplifyRatNeg(final RatNegExpr expr) {
		final Expr<RatType> op = simplify(expr.getOp());

		if (op instanceof RatLitExpr) {
			final RatLitExpr litOp = (RatLitExpr) op;
			return litOp.neg();
		} else if (op instanceof RatNegExpr) {
			final RatNegExpr negOp = (RatNegExpr) op;
			return negOp.getOp();
		}

		return expr.with(op);
	}

	private Expr<RatType> simplifyRatMul(final RatMulExpr expr) {
		final List<Expr<RatType>> ops = new ArrayList<>();
		int num = 1;
		int denom = 1;

		for (final Expr<RatType> op : expr.getOps()) {
			final Expr<RatType> opVisited = simplify(op);
			if (opVisited instanceof RatLitExpr) {
				final RatLitExpr litOp = (RatLitExpr) opVisited;
				num *= litOp.getNum();
				denom *= litOp.getDenom();

				if (num == 0) {
					return Rat(0, 1);
				}

			} else if (opVisited instanceof RatMulExpr) {
				final RatMulExpr mulOp = (RatMulExpr) opVisited;
				ops.addAll(mulOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		final Expr<RatType> prod = Rat(num, denom);

		if (!prod.equals(Rat(1, 1))) {
			ops.add(0, prod);
		}

		if (ops.size() == 0) {
			return Rat(1, 1);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private Expr<RatType> simplifyRatDiv(final RatDivExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return leftLit.div(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyRatEq(final RatEqExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			return Bool(leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyRatNeq(final RatNeqExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			return Bool(!leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return False();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyRatGeq(final RatGeqExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) >= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return True();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyRatGt(final RatGtExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) > 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return False();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyRatLeq(final RatLeqExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) <= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return True();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyRatLt(final RatLtExpr expr) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp());
		final Expr<RatType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) < 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return False();
		}

		return expr.with(leftOp, rightOp);
	}

	/*
	 * Integers
	 */

	private Expr<RatType> simplifyIntToRat(final IntToRatExpr expr) {
		final Expr<IntType> op = simplify(expr.getOp());

		if (op instanceof IntLitExpr) {
			final IntLitExpr litOp = (IntLitExpr) op;
			return litOp.toRat();
		}

		return expr.with(op);
	}

	private Expr<IntType> simplifyIntAdd(final IntAddExpr expr) {
		final List<Expr<IntType>> ops = new ArrayList<>();
		int value = 0;

		for (final Expr<IntType> op : expr.getOps()) {
			final Expr<IntType> opVisited = simplify(op);
			if (opVisited instanceof IntLitExpr) {
				final IntLitExpr litOp = (IntLitExpr) opVisited;
				value = value + litOp.getValue();
			} else if (opVisited instanceof IntAddExpr) {
				final IntAddExpr addOp = (IntAddExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		if (value != 0) {
			final Expr<IntType> sum = Int(value);
			ops.add(sum);
		}

		if (ops.size() == 0) {
			return Int(0);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private Expr<IntType> simplifyIntSub(final IntSubExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return leftLit.sub(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return Int(0);
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<IntType> simplifyIntNeg(final IntNegExpr expr) {
		final Expr<IntType> op = simplify(expr.getOp());

		if (op instanceof IntLitExpr) {
			final IntLitExpr litOp = (IntLitExpr) op;
			return litOp.neg();
		} else if (op instanceof IntNegExpr) {
			final IntNegExpr negOp = (IntNegExpr) op;
			return negOp.getOp();
		}

		return expr.with(op);
	}

	private Expr<IntType> simplifyIntMul(final IntMulExpr expr) {
		final List<Expr<IntType>> ops = new ArrayList<>();
		int value = 1;

		for (final Expr<IntType> op : expr.getOps()) {
			final Expr<IntType> opVisited = simplify(op);
			if (opVisited instanceof IntLitExpr) {
				final IntLitExpr litOp = (IntLitExpr) opVisited;
				value = value * litOp.getValue();

				if (value == 0) {
					return Int(0);
				}

			} else if (opVisited instanceof IntMulExpr) {
				final IntMulExpr mulOp = (IntMulExpr) opVisited;
				ops.addAll(mulOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		if (value != 1) {
			final Expr<IntType> prod = Int(value);
			ops.add(0, prod);
		}

		if (ops.size() == 0) {
			return Int(1);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private Expr<IntType> simplifyIntDiv(final IntDivExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return leftLit.div(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<IntType> simplifyMod(final ModExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return leftLit.mod(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyIntEq(final IntEqExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			return Bool(leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyIntNeq(final IntNeqExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			return Bool(!leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return False();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyIntGeq(final IntGeqExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) >= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return True();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyIntGt(final IntGtExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) > 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return False();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyIntLeq(final IntLeqExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) <= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return True();
		}

		return expr.with(leftOp, rightOp);
	}

	private Expr<BoolType> simplifyIntLt(final IntLtExpr expr) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp());
		final Expr<IntType> rightOp = simplify(expr.getRightOp());

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) < 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp))
				return False();
		}

		return expr.with(leftOp, rightOp);
	}

}
