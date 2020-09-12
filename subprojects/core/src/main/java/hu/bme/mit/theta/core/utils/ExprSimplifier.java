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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.common.DispatchTable2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvConcatExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvPosExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntPosExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
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
import hu.bme.mit.theta.core.type.rattype.RatPosExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class ExprSimplifier {

	private static final DispatchTable2<Valuation, Expr<?>> TABLE = DispatchTable2.<Valuation, Expr<?>>builder()

			// Boolean

			.addCase(NotExpr.class, ExprSimplifier::simplifyNot)

			.addCase(ImplyExpr.class, ExprSimplifier::simplifyImply)

			.addCase(IffExpr.class, ExprSimplifier::simplifyIff)

			.addCase(XorExpr.class, ExprSimplifier::simplifyXor)

			.addCase(AndExpr.class, ExprSimplifier::simplifyAnd)

			.addCase(OrExpr.class, ExprSimplifier::simplifyOr)

			// Rational

			.addCase(RatAddExpr.class, ExprSimplifier::simplifyRatAdd)

			.addCase(RatSubExpr.class, ExprSimplifier::simplifyRatSub)

			.addCase(RatPosExpr.class, ExprSimplifier::simplifyRatPos)

			.addCase(RatNegExpr.class, ExprSimplifier::simplifyRatNeg)

			.addCase(RatMulExpr.class, ExprSimplifier::simplifyRatMul)

			.addCase(RatDivExpr.class, ExprSimplifier::simplifyRatDiv)

			.addCase(RatEqExpr.class, ExprSimplifier::simplifyRatEq)

			.addCase(RatNeqExpr.class, ExprSimplifier::simplifyRatNeq)

			.addCase(RatGeqExpr.class, ExprSimplifier::simplifyRatGeq)

			.addCase(RatGtExpr.class, ExprSimplifier::simplifyRatGt)

			.addCase(RatLeqExpr.class, ExprSimplifier::simplifyRatLeq)

			.addCase(RatLtExpr.class, ExprSimplifier::simplifyRatLt)

			// Integer

			.addCase(IntToRatExpr.class, ExprSimplifier::simplifyIntToRat)

			.addCase(IntAddExpr.class, ExprSimplifier::simplifyIntAdd)

			.addCase(IntSubExpr.class, ExprSimplifier::simplifyIntSub)

			.addCase(IntPosExpr.class, ExprSimplifier::simplifyIntPos)

			.addCase(IntNegExpr.class, ExprSimplifier::simplifyIntNeg)

			.addCase(IntMulExpr.class, ExprSimplifier::simplifyIntMul)

			.addCase(IntDivExpr.class, ExprSimplifier::simplifyIntDiv)

			.addCase(IntModExpr.class, ExprSimplifier::simplifyMod)

			.addCase(IntEqExpr.class, ExprSimplifier::simplifyIntEq)

			.addCase(IntNeqExpr.class, ExprSimplifier::simplifyIntNeq)

			.addCase(IntGeqExpr.class, ExprSimplifier::simplifyIntGeq)

			.addCase(IntGtExpr.class, ExprSimplifier::simplifyIntGt)

			.addCase(IntLeqExpr.class, ExprSimplifier::simplifyIntLeq)

			.addCase(IntLtExpr.class, ExprSimplifier::simplifyIntLt)

			// Array

			.addCase(ArrayReadExpr.class, ExprSimplifier::simplifyArrayRead)

			.addCase(ArrayWriteExpr.class, ExprSimplifier::simplifyArrayWrite)

			// Bitvectors

			.addCase(BvConcatExpr.class, ExprSimplifier::simplifyBvConcat)

			.addCase(BvExtractExpr.class, ExprSimplifier::simplifyBvExtract)

			.addCase(BvZExtExpr.class, ExprSimplifier::simplifyBvZExt)

			.addCase(BvSExtExpr.class, ExprSimplifier::simplifyBvSExt)

			.addCase(BvAddExpr.class, ExprSimplifier::simplifyBvAdd)

			.addCase(BvSubExpr.class, ExprSimplifier::simplifyBvSub)

			.addCase(BvPosExpr.class, ExprSimplifier::simplifyBvPos)

			.addCase(BvNegExpr.class, ExprSimplifier::simplifyBvNeg)

			.addCase(BvMulExpr.class, ExprSimplifier::simplifyBvMul)

			.addCase(BvUDivExpr.class, ExprSimplifier::simplifyBvUDiv)

			.addCase(BvSDivExpr.class, ExprSimplifier::simplifyBvSDiv)

			.addCase(BvSModExpr.class, ExprSimplifier::simplifyBvSMod)

			.addCase(BvURemExpr.class, ExprSimplifier::simplifyBvURem)

			.addCase(BvSRemExpr.class, ExprSimplifier::simplifyBvSRem)

			.addCase(BvAndExpr.class, ExprSimplifier::simplifyBvAnd)

			.addCase(BvOrExpr.class, ExprSimplifier::simplifyBvOr)

			.addCase(BvXorExpr.class, ExprSimplifier::simplifyBvXor)

			.addCase(BvNotExpr.class, ExprSimplifier::simplifyBvNot)

			.addCase(BvShiftLeftExpr.class, ExprSimplifier::simplifyBvShiftLeft)

			.addCase(BvArithShiftRightExpr.class, ExprSimplifier::simplifyBvArithShiftRight)

			.addCase(BvLogicShiftRightExpr.class, ExprSimplifier::simplifyBvLogicShiftRight)

			.addCase(BvRotateLeftExpr.class, ExprSimplifier::simplifyBvRotateLeft)

			.addCase(BvRotateRightExpr.class, ExprSimplifier::simplifyBvRotateRight)

			.addCase(BvEqExpr.class, ExprSimplifier::simplifyBvEq)

			.addCase(BvNeqExpr.class, ExprSimplifier::simplifyBvNeq)

			.addCase(BvUGeqExpr.class, ExprSimplifier::simplifyBvUGeq)

			.addCase(BvUGtExpr.class, ExprSimplifier::simplifyBvUGt)

			.addCase(BvULeqExpr.class, ExprSimplifier::simplifyBvULeq)

			.addCase(BvULtExpr.class, ExprSimplifier::simplifyBvULt)

			.addCase(BvSGeqExpr.class, ExprSimplifier::simplifyBvSGeq)

			.addCase(BvSGtExpr.class, ExprSimplifier::simplifyBvSGt)

			.addCase(BvSLeqExpr.class, ExprSimplifier::simplifyBvSLeq)

			.addCase(BvSLtExpr.class, ExprSimplifier::simplifyBvSLt)

			// General

			.addCase(RefExpr.class, ExprSimplifier::simplifyRef)

			.addCase(IteExpr.class, ExprSimplifier::simplifyIte)

			// Default

			.addDefault((o, val) -> {
				final Expr<?> expr = (Expr<?>) o;
				return expr.map(e -> simplify(e, val));
			})

			.build();

	private ExprSimplifier() {
	}

	@SuppressWarnings("unchecked")
	public static <T extends Type> Expr<T> simplify(final Expr<T> expr, final Valuation valuation) {
		return (Expr<T>) TABLE.dispatch(expr, valuation);
	}

	/*
	 * General
	 */

	private static Expr<?> simplifyRef(final RefExpr<?> expr, final Valuation val) {
		return simplifyGenericRef(expr, val);
	}

	// TODO Eliminate helper method once the Java compiler is able to handle
	// this kind of type inference
	private static <DeclType extends Type> Expr<DeclType> simplifyGenericRef(final RefExpr<DeclType> expr,
																			 final Valuation val) {
		final Optional<LitExpr<DeclType>> eval = val.eval(expr.getDecl());
		if (eval.isPresent()) {
			return eval.get();
		}

		return expr;
	}

	private static Expr<?> simplifyIte(final IteExpr<?> expr, final Valuation val) {
		return simplifyGenericIte(expr, val);
	}

	// TODO Eliminate helper method once the Java compiler is able to handle
	// this kind of type inference
	private static <ExprType extends Type> Expr<ExprType> simplifyGenericIte(final IteExpr<ExprType> expr,
																			 final Valuation val) {
		final Expr<BoolType> cond = simplify(expr.getCond(), val);

		if (cond instanceof TrueExpr) {
			final Expr<ExprType> then = simplify(expr.getThen(), val);
			return then;

		} else if (cond instanceof FalseExpr) {
			final Expr<ExprType> elze = simplify(expr.getElse(), val);
			return elze;
		}

		final Expr<ExprType> then = simplify(expr.getThen(), val);
		final Expr<ExprType> elze = simplify(expr.getElse(), val);

		return expr.with(cond, then, elze);
	}

	private static Expr<?> simplifyArrayRead(final ArrayReadExpr<?, ?> expr, final Valuation val) {
		return simplifyGenericArrayRead(expr, val);
	}

	private static <IT extends Type, ET extends Type> Expr<ET>
		simplifyGenericArrayRead(final ArrayReadExpr<IT, ET> expr, final Valuation val) {
		Expr<ArrayType<IT, ET>> arr = simplify(expr.getArray(), val);
		Expr<IT> index = simplify(expr.getIndex(), val);
		if (arr instanceof LitExpr<?> && index instanceof LitExpr<?>){
			return (LitExpr<ET>)expr.eval(val);
		}
		return expr.with(arr, index);
	}

	private static Expr<?> simplifyArrayWrite(final ArrayWriteExpr<?, ?> expr, final Valuation val) {
		return simplifyGenericArrayWrite(expr, val);
	}

	private static <IT extends Type, ET extends Type> Expr<ArrayType<IT, ET>>
	simplifyGenericArrayWrite(final ArrayWriteExpr<IT, ET> expr, final Valuation val) {
		Expr<ArrayType<IT, ET>> arr = simplify(expr.getArray(), val);
		Expr<IT> index = simplify(expr.getIndex(), val);
		Expr<ET> elem = simplify(expr.getElem(), val);
		if (arr instanceof LitExpr<?> && index instanceof LitExpr<?> && elem instanceof  LitExpr<?>){
			return expr.eval(val);
		}
		return expr.with(arr, index, elem);
	}

	/*
	 * Booleans
	 */

	private static Expr<BoolType> simplifyNot(final NotExpr expr, final Valuation val) {
		final Expr<BoolType> op = simplify(expr.getOp(), val);
		if (op instanceof NotExpr) {
			return ((NotExpr) op).getOp();
		} else if (op instanceof TrueExpr) {
			return False();
		} else if (op instanceof FalseExpr) {
			return True();
		}

		return expr.with(op);
	}

	private static Expr<BoolType> simplifyImply(final ImplyExpr expr, final Valuation val) {
		final Expr<BoolType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BoolType> rightOp = simplify(expr.getRightOp(), val);

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
			return simplify(Not(leftOp), val);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyIff(final IffExpr expr, final Valuation val) {
		final Expr<BoolType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BoolType> rightOp = simplify(expr.getRightOp(), val);

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
			return simplify(Not(rightOp), val);
		} else if (rightOp instanceof FalseExpr) {
			return simplify(Not(leftOp), val);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyXor(final XorExpr expr, final Valuation val) {
		final Expr<BoolType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BoolType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BoolLitExpr && rightOp instanceof BoolLitExpr) {
			final boolean leftValue = ((BoolLitExpr) leftOp).getValue();
			final boolean rightValue = ((BoolLitExpr) rightOp).getValue();
			return Bool(leftValue != rightValue);
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		if (leftOp instanceof TrueExpr) {
			return simplify(Not(rightOp), val);
		} else if (rightOp instanceof TrueExpr) {
			return simplify(Not(leftOp), val);
		} else if (leftOp instanceof FalseExpr) {
			return rightOp;
		} else if (rightOp instanceof FalseExpr) {
			return leftOp;
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyAnd(final AndExpr expr, final Valuation val) {
		final List<Expr<BoolType>> ops = new ArrayList<>();

		if (expr.getOps().isEmpty()) {
			return True();
		}

		for (final Expr<BoolType> op : expr.getOps()) {
			final Expr<BoolType> opVisited = simplify(op, val);
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

		if (ops.isEmpty()) {
			return True();
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<BoolType> simplifyOr(final OrExpr expr, final Valuation val) {
		final List<Expr<BoolType>> ops = new ArrayList<>();

		if (expr.getOps().isEmpty()) {
			return True();
		}

		for (final Expr<BoolType> op : expr.getOps()) {
			final Expr<BoolType> opVisited = simplify(op, val);
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

		if (ops.isEmpty()) {
			return False();
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	/*
	 * Rationals
	 */

	private static Expr<RatType> simplifyRatAdd(final RatAddExpr expr, final Valuation val) {
		final List<Expr<RatType>> ops = new ArrayList<>();

		for (final Expr<RatType> op : expr.getOps()) {
			final Expr<RatType> opVisited = simplify(op, val);
			if (opVisited instanceof RatAddExpr) {
				final RatAddExpr addOp = (RatAddExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		var num = BigInteger.ZERO;
		var denom = BigInteger.ONE;

		for (final Iterator<Expr<RatType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<RatType> op = iterator.next();
			if (op instanceof RatLitExpr) {
				final RatLitExpr litOp = (RatLitExpr) op;
				num = num.multiply(litOp.getDenom()).add(denom.multiply(litOp.getNum()));
				denom = denom.multiply(litOp.getDenom());
				iterator.remove();
			}
		}

		final Expr<RatType> sum = Rat(num, denom);

		if (!sum.equals(Rat(0, 1))) {
			ops.add(0, sum);
		}

		if (ops.isEmpty()) {
			return Rat(0, 1);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<RatType> simplifyRatSub(final RatSubExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return leftLit.sub(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return Rat(0, 1);
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<RatType> simplifyRatPos(final RatPosExpr expr, final Valuation val) {
		return simplify(expr.getOp(), val);
	}

	private static Expr<RatType> simplifyRatNeg(final RatNegExpr expr, final Valuation val) {
		final Expr<RatType> op = simplify(expr.getOp(), val);

		if (op instanceof RatLitExpr) {
			final RatLitExpr litOp = (RatLitExpr) op;
			return litOp.neg();
		} else if (op instanceof RatNegExpr) {
			final RatNegExpr negOp = (RatNegExpr) op;
			return negOp.getOp();
		}

		return expr.with(op);
	}

	private static Expr<RatType> simplifyRatMul(final RatMulExpr expr, final Valuation val) {
		final List<Expr<RatType>> ops = new ArrayList<>();

		for (final Expr<RatType> op : expr.getOps()) {
			final Expr<RatType> opVisited = simplify(op, val);
			if (opVisited instanceof RatMulExpr) {
				final RatMulExpr mulOp = (RatMulExpr) opVisited;
				ops.addAll(mulOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		var num = BigInteger.ONE;
		var denom = BigInteger.ONE;

		for (final Iterator<Expr<RatType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<RatType> op = iterator.next();
			if (op instanceof RatLitExpr) {
				final RatLitExpr litOp = (RatLitExpr) op;
				num = num.multiply(litOp.getNum());
				denom = denom.multiply(litOp.getDenom());
				iterator.remove();
				if (num.compareTo(BigInteger.ZERO) == 0) {
					return Rat(0, 1);
				}
			}
		}

		final Expr<RatType> prod = Rat(num, denom);

		if (!prod.equals(Rat(1, 1))) {
			ops.add(0, prod);
		}

		if (ops.isEmpty()) {
			return Rat(1, 1);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<RatType> simplifyRatDiv(final RatDivExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return leftLit.div(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyRatEq(final RatEqExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			return Bool(leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyRatNeq(final RatNeqExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			return Bool(!leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyRatGeq(final RatGeqExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) >= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyRatGt(final RatGtExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) > 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyRatLeq(final RatLeqExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) <= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyRatLt(final RatLtExpr expr, final Valuation val) {
		final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
			final RatLitExpr leftLit = (RatLitExpr) leftOp;
			final RatLitExpr rightLit = (RatLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) < 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	/*
	 * Integers
	 */

	private static Expr<RatType> simplifyIntToRat(final IntToRatExpr expr, final Valuation val) {
		final Expr<IntType> op = simplify(expr.getOp(), val);

		if (op instanceof IntLitExpr) {
			final IntLitExpr litOp = (IntLitExpr) op;
			return litOp.toRat();
		}

		return expr.with(op);
	}

	private static Expr<IntType> simplifyIntAdd(final IntAddExpr expr, final Valuation val) {
		final List<Expr<IntType>> ops = new ArrayList<>();

		for (final Expr<IntType> op : expr.getOps()) {
			final Expr<IntType> opVisited = simplify(op, val);
			if (opVisited instanceof IntAddExpr) {
				final IntAddExpr addOp = (IntAddExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		var value = BigInteger.ZERO;

		for (final Iterator<Expr<IntType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<IntType> op = iterator.next();
			if (op instanceof IntLitExpr) {
				final IntLitExpr litOp = (IntLitExpr) op;
				value = value.add(litOp.getValue());
				iterator.remove();
			}
		}

		if (value.compareTo(BigInteger.ZERO) != 0) {
			final Expr<IntType> sum = Int(value);
			ops.add(sum);
		}

		if (ops.isEmpty()) {
			return Int(BigInteger.ZERO);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<IntType> simplifyIntSub(final IntSubExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return leftLit.sub(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return Int(BigInteger.ZERO);
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<IntType> simplifyIntPos(final IntPosExpr expr, final Valuation val) {
		return simplify(expr.getOp(), val);
	}

	private static Expr<IntType> simplifyIntNeg(final IntNegExpr expr, final Valuation val) {
		final Expr<IntType> op = simplify(expr.getOp(), val);

		if (op instanceof IntLitExpr) {
			final IntLitExpr litOp = (IntLitExpr) op;
			return litOp.neg();
		} else if (op instanceof IntNegExpr) {
			final IntNegExpr negOp = (IntNegExpr) op;
			return negOp.getOp();
		}

		return expr.with(op);
	}

	private static Expr<IntType> simplifyIntMul(final IntMulExpr expr, final Valuation val) {
		final List<Expr<IntType>> ops = new ArrayList<>();

		for (final Expr<IntType> op : expr.getOps()) {
			final Expr<IntType> opVisited = simplify(op, val);
			if (opVisited instanceof IntMulExpr) {
				final IntMulExpr mulOp = (IntMulExpr) opVisited;
				ops.addAll(mulOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		var value = BigInteger.ONE;
		for (final Iterator<Expr<IntType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<IntType> op = iterator.next();
			if (op instanceof IntLitExpr) {
				final IntLitExpr litOp = (IntLitExpr) op;
				value = value.multiply(litOp.getValue());
				iterator.remove();
				if (value.compareTo(BigInteger.ZERO) == 0) {
					return Int(BigInteger.ZERO);
				}
			}
		}

		if (value.compareTo(BigInteger.ONE) != 0) {
			final Expr<IntType> prod = Int(value);
			ops.add(0, prod);
		}

		if (ops.isEmpty()) {
			return Int(BigInteger.ONE);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<IntType> simplifyIntDiv(final IntDivExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return leftLit.div(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<IntType> simplifyMod(final IntModExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return leftLit.mod(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyIntEq(final IntEqExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			return Bool(leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyIntNeq(final IntNeqExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			return Bool(!leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyIntGeq(final IntGeqExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) >= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyIntGt(final IntGtExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) > 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyIntLeq(final IntLeqExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) <= 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyIntLt(final IntLtExpr expr, final Valuation val) {
		final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Bool(leftLit.compareTo(rightLit) < 0);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	/*
	 * Bitvectors
	 */

	private static Expr<BvType> simplifyBvConcat(final BvConcatExpr expr, final Valuation val) {
		final List<Expr<BvType>> ops = new ArrayList<>();

		for (final Expr<BvType> op : expr.getOps()) {
			final Expr<BvType> opVisited = simplify(op, val);
			if (opVisited instanceof BvConcatExpr) {
				final BvConcatExpr addOp = (BvConcatExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		BvLitExpr value = null;

		for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<BvType> op = iterator.next();
			if (op instanceof BvLitExpr) {
				final BvLitExpr litOp = (BvLitExpr) op;
				if(value == null) {
					value = litOp;
				}
				else {
					value = value.concat(litOp);
				}
				iterator.remove();
			}
			else {
				return expr.withOps(ops);
			}
		}

		return value;
	}

	private static Expr<BvType> simplifyBvExtract(final BvExtractExpr expr, final Valuation val) {
		final Expr<BvType> bitvec = simplify(expr.getBitvec(), val);

		if(bitvec instanceof BvLitExpr) {
			return ((BvLitExpr) bitvec).extract(expr.getFrom(), expr.getUntil());
		}
		else {
			return expr;
		}
	}

	private static Expr<BvType> simplifyBvZExt(final BvZExtExpr expr, final Valuation val) {
		final Expr<BvType> bitvec = simplify(expr.getOp(), val);

		if(bitvec instanceof BvLitExpr) {
			return ((BvLitExpr) bitvec).zext(expr.getExtendType());
		}
		else {
			return expr;
		}
	}

	private static Expr<BvType> simplifyBvSExt(final BvSExtExpr expr, final Valuation val) {
		final Expr<BvType> bitvec = simplify(expr.getOp(), val);

		if(bitvec instanceof BvLitExpr) {
			return ((BvLitExpr) bitvec).sext(expr.getExtendType());
		}
		else {
			return expr;
		}
	}

	private static Expr<BvType> simplifyBvAdd(final BvAddExpr expr, final Valuation val) {
		final List<Expr<BvType>> ops = new ArrayList<>();

		for (final Expr<BvType> op : expr.getOps()) {
			final Expr<BvType> opVisited = simplify(op, val);
			if (opVisited instanceof BvAddExpr) {
				final BvAddExpr addOp = (BvAddExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		BvLitExpr value = Bv(new boolean[expr.getType().getSize()]);

		for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<BvType> op = iterator.next();
			if (op instanceof BvLitExpr) {
				final BvLitExpr litOp = (BvLitExpr) op;
				value = value.add(litOp);
				iterator.remove();
			}
		}

		if (!value.eq(Bv(new boolean[expr.getType().getSize()])).getValue()) {
			ops.add(value);
		}

		if (ops.isEmpty()) {
			return Bv(new boolean[expr.getType().getSize()]);
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<BvType> simplifyBvSub(final BvSubExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.sub(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return Bv(new boolean[expr.getType().getSize()]);
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvPos(final BvPosExpr expr, final Valuation val) {
		return simplify(expr.getOp(), val);
	}

	private static Expr<BvType> simplifyBvNeg(final BvNegExpr expr, final Valuation val) {
		final Expr<BvType> op = simplify(expr.getOp(), val);

		if (op instanceof BvLitExpr) {
			final BvLitExpr litOp = (BvLitExpr) op;
			return litOp.neg();
		} else if (op instanceof BvNegExpr) {
			final BvNegExpr negOp = (BvNegExpr) op;
			return negOp.getOp();
		}

		return expr.with(op);
	}

	private static Expr<BvType> simplifyBvMul(final BvMulExpr expr, final Valuation val) {
		final List<Expr<BvType>> ops = new ArrayList<>();

		for (final Expr<BvType> op : expr.getOps()) {
			final Expr<BvType> opVisited = simplify(op, val);
			if (opVisited instanceof BvMulExpr) {
				final BvMulExpr mulOp = (BvMulExpr) opVisited;
				ops.addAll(mulOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}

		final BvLitExpr ZERO = Bv(new boolean[expr.getType().getSize()]);
		final BvLitExpr ONE = Bv(new boolean[expr.getType().getSize()]);
		ONE.getValue()[expr.getType().getSize()-1] = true; // 1

		BvLitExpr value = ONE;
		for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<BvType> op = iterator.next();
			if (op instanceof BvLitExpr) {
				final BvLitExpr litOp = (BvLitExpr) op;
				value = value.mul(litOp);
				iterator.remove();
				if (value.equals(ZERO)) {
					return ZERO;
				}
			}
		}

		if (!value.equals(ONE)) {
			ops.add(0, value);
		}

		if (ops.isEmpty()) {
			return ONE;
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<BvType> simplifyBvUDiv(final BvUDivExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.udiv(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				final BvLitExpr ONE = Bv(new boolean[expr.getType().getSize()]);
				ONE.getValue()[expr.getType().getSize()-1] = true; // 1
				return ONE;
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvSDiv(final BvSDivExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.sdiv(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				final BvLitExpr ONE = Bv(new boolean[expr.getType().getSize()]);
				ONE.getValue()[expr.getType().getSize()-1] = true; // 1
				return ONE;
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvSMod(final BvSModExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.smod(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return Bv(new boolean[expr.getType().getSize()]);
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvURem(final BvURemExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.urem(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return Bv(new boolean[expr.getType().getSize()]);
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvSRem(final BvSRemExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.srem(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return Bv(new boolean[expr.getType().getSize()]);
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvAnd(final BvAndExpr expr, final Valuation val) {
		final List<Expr<BvType>> ops = new ArrayList<>();

		for (final Expr<BvType> op : expr.getOps()) {
			final Expr<BvType> opVisited = simplify(op, val);
			if (opVisited instanceof BvAndExpr) {
				final BvAndExpr addOp = (BvAndExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		BvLitExpr ONES = Bv(new boolean[expr.getType().getSize()]);
		for(int i = 0; i < expr.getType().getSize(); i++) {
			ONES.getValue()[i] = true;
		}

		BvLitExpr value = ONES;

		for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<BvType> op = iterator.next();
			if (op instanceof BvLitExpr) {
				final BvLitExpr litOp = (BvLitExpr) op;
				value = value.and(litOp);
				iterator.remove();
			}
		}

		if (!value.equals(ONES)) {
			ops.add(value);
		}

		if (ops.isEmpty()) {
			return ONES;
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<BvType> simplifyBvOr(final BvOrExpr expr, final Valuation val) {
		final List<Expr<BvType>> ops = new ArrayList<>();

		for (final Expr<BvType> op : expr.getOps()) {
			final Expr<BvType> opVisited = simplify(op, val);
			if (opVisited instanceof BvOrExpr) {
				final BvOrExpr addOp = (BvOrExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		BvLitExpr ZEROS = Bv(new boolean[expr.getType().getSize()]);

		BvLitExpr value = ZEROS;

		for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<BvType> op = iterator.next();
			if (op instanceof BvLitExpr) {
				final BvLitExpr litOp = (BvLitExpr) op;
				value = value.or(litOp);
				iterator.remove();
			}
		}

		if (!value.equals(ZEROS)) {
			ops.add(value);
		}

		if (ops.isEmpty()) {
			return ZEROS;
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<BvType> simplifyBvXor(final BvXorExpr expr, final Valuation val) {
		final List<Expr<BvType>> ops = new ArrayList<>();

		for (final Expr<BvType> op : expr.getOps()) {
			final Expr<BvType> opVisited = simplify(op, val);
			if (opVisited instanceof BvXorExpr) {
				final BvXorExpr addOp = (BvXorExpr) opVisited;
				ops.addAll(addOp.getOps());
			} else {
				ops.add(opVisited);
			}
		}
		BvLitExpr ZEROS = Bv(new boolean[expr.getType().getSize()]);

		BvLitExpr value = ZEROS;

		for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
			final Expr<BvType> op = iterator.next();
			if (op instanceof BvLitExpr) {
				final BvLitExpr litOp = (BvLitExpr) op;
				value = value.xor(litOp);
				iterator.remove();
			}
		}

		if (!value.equals(ZEROS)) {
			ops.add(value);
		}

		if (ops.isEmpty()) {
			return ZEROS;
		} else if (ops.size() == 1) {
			return Utils.singleElementOf(ops);
		}

		return expr.with(ops);
	}

	private static Expr<BvType> simplifyBvNot(final BvNotExpr expr, final Valuation val) {
		final Expr<BvType> op = simplify(expr.getOp(), val);

		if (op instanceof BvLitExpr) {
			final BvLitExpr litOp = (BvLitExpr) op;
			return litOp.not();
		} else if (op instanceof BvNotExpr) {
			final BvNotExpr notOp = (BvNotExpr) op;
			return notOp.getOp();
		}

		return expr.with(op);
	}

	private static Expr<BvType> simplifyBvShiftLeft(final BvShiftLeftExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.shiftLeft(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvArithShiftRight(final BvArithShiftRightExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.arithShiftRight(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvLogicShiftRight(final BvLogicShiftRightExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.logicShiftRight(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvRotateLeft(final BvRotateLeftExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.rotateLeft(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BvType> simplifyBvRotateRight(final BvRotateRightExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.rotateRight(rightLit);
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvEq(final BvEqExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			return Bool(leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvNeq(final BvNeqExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			return Bool(!leftOp.equals(rightOp));
		} else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvUGeq(final BvUGeqExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.uge(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvUGt(final BvUGtExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.ugt(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvULeq(final BvULeqExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.ule(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvULt(final BvULtExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.ult(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvSGeq(final BvSGeqExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.sge(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvSGt(final BvSGtExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.sgt(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvSLeq(final BvSLeqExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.sle(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return True();
			}
		}

		return expr.with(leftOp, rightOp);
	}

	private static Expr<BoolType> simplifyBvSLt(final BvSLtExpr expr, final Valuation val) {
		final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
		final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

		if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
			final BvLitExpr leftLit = (BvLitExpr) leftOp;
			final BvLitExpr rightLit = (BvLitExpr) rightOp;
			return leftLit.slt(rightLit);
		}

		if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
			if (leftOp.equals(rightOp)) {
				return False();
			}
		}

		return expr.with(leftOp, rightOp);
	}

}
