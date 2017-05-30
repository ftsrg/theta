package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;

public final class Exprs {

	private Exprs() {
	}

	public static <DeclType extends Type> RefExpr<DeclType> Ref(final Decl<DeclType> decl) {
		return new RefExpr<>(decl);
	}

	public static <ReturnType extends Type> ProcCallExpr<ReturnType> Call(
			final Expr<? extends ProcType<? extends ReturnType>> proc, final List<? extends Expr<?>> params) {
		return new ProcCallExpr<>(proc, params);
	}

	public static <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op) {
		return new PrimedExpr<>(op);
	}

	public static EqExpr Eq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		return new EqExpr(leftOp, rightOp);
	}

	public static NeqExpr Neq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		return new NeqExpr(leftOp, rightOp);
	}

	public static LtExpr Lt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new LtExpr(leftOp, rightOp);
	}

	public static LeqExpr Leq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new LeqExpr(leftOp, rightOp);
	}

	public static GtExpr Gt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new GtExpr(leftOp, rightOp);
	}

	public static GeqExpr Geq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new GeqExpr(leftOp, rightOp);
	}

	public static <T extends ClosedUnderNeg> NegExpr<T> Neg(final Expr<? extends T> op) {
		return new NegExpr<>(op);
	}

	public static <T extends ClosedUnderSub> SubExpr<T> Sub(final Expr<? extends T> leftOp,
			final Expr<? extends T> rightOp) {
		return new SubExpr<>(leftOp, rightOp);
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Collection<? extends Expr<? extends T>> ops) {
		return new AddExpr<>(ops);
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Collection<? extends Expr<? extends T>> ops) {
		return new MulExpr<>(ops);
	}

	public static <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze) {
		return new IteExpr<>(cond, then, elze);
	}

	/*
	 * Convenience methods
	 */

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2) {
		return Add(ImmutableList.of(op1, op2));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3) {
		return Add(ImmutableList.of(op1, op2, op3));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4) {
		return Add(ImmutableList.of(op1, op2, op3, op4));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4, final Expr<? extends T> op5) {
		return Add(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2) {
		return Mul(ImmutableList.of(op1, op2));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3) {
		return Mul(ImmutableList.of(op1, op2, op3));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4) {
		return Mul(ImmutableList.of(op1, op2, op3, op4));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4, final Expr<? extends T> op5) {
		return Mul(ImmutableList.of(op1, op2, op3, op4, op5));
	}

	////

	public static <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op, final int i) {
		checkArgument(i > 0);
		if (i == 1) {
			return new PrimedExpr<>(op);
		} else {
			return new PrimedExpr<>(Prime(op, i - 1));
		}
	}

}
