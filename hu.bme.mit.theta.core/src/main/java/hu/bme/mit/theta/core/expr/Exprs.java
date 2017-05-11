package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.FuncType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;

public final class Exprs {

	private static final TrueExpr TRUE_EXPR;
	private static final FalseExpr FALSE_EXPR;

	static {
		TRUE_EXPR = new TrueExpr();
		FALSE_EXPR = new FalseExpr();
	}

	private Exprs() {
	}

	public static TrueExpr True() {
		return TRUE_EXPR;
	}

	public static FalseExpr False() {
		return FALSE_EXPR;
	}

	public static BoolLitExpr Bool(final boolean value) {
		if (value)
			return True();
		return False();
	}

	public static IntLitExpr Int(final int value) {
		return new IntLitExpr(value);
	}

	public static RatLitExpr Rat(final int num, final int denom) {
		return new RatLitExpr(num, denom);
	}

	public static <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(
			final ParamDecl<? super P> paramDecl, final Expr<? extends R> result) {
		return new FuncLitExpr<P, R>(paramDecl, result);
	}

	public static <P extends Type, R extends Type> FuncAppExpr<P, R> App(
			final Expr<? extends FuncType<? super P, ? extends R>> func, final Expr<? extends P> param) {
		return new FuncAppExpr<>(func, param);
	}

	public static <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index) {
		return new ArrayReadExpr<>(array, index);
	}

	public static <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index,
			final Expr<? extends E> elem) {
		return new ArrayWriteExpr<>(array, index, elem);
	}

	public static <ReturnType extends Type> ProcCallExpr<ReturnType> Call(
			final Expr<? extends ProcType<? extends ReturnType>> proc, final List<? extends Expr<?>> params) {
		return new ProcCallExpr<>(proc, params);
	}

	public static <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op) {
		return new PrimedExpr<>(op);
	}

	public static NotExpr Not(final Expr<? extends BoolType> op) {
		return new NotExpr(op);
	}

	public static ImplyExpr Imply(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		return new ImplyExpr(leftOp, rightOp);
	}

	public static IffExpr Iff(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		return new IffExpr(leftOp, rightOp);
	}

	public static AndExpr And(final Collection<? extends Expr<? extends BoolType>> ops) {
		return new AndExpr(ops);
	}

	public static OrExpr Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		return new OrExpr(ops);
	}

	public static ForallExpr Forall(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		return new ForallExpr(paramDecls, op);
	}

	public static ExistsExpr Exists(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		return new ExistsExpr(paramDecls, op);
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

	public static ModExpr Mod(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return new ModExpr(leftOp, rightOp);
	}

	public static RemExpr Rem(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return new RemExpr(leftOp, rightOp);
	}

	public static IntDivExpr IntDiv(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return new IntDivExpr(leftOp, rightOp);
	}

	public static RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return new RatDivExpr(leftOp, rightOp);
	}

	public static <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze) {
		return new IteExpr<>(cond, then, elze);
	}

	/*
	 * Convenience methods
	 */

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		return And(ImmutableSet.of(op1, op2));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		return And(ImmutableSet.of(op1, op2, op3));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		return And(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		return And(ImmutableSet.of(op1, op2, op3, op4, op5));
	}

	////

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		return Or(ImmutableSet.of(op1, op2));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		return Or(ImmutableSet.of(op1, op2, op3));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		return Or(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		return Or(ImmutableSet.of(op1, op2, op3, op4, op5));
	}

	////

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2) {
		return Add(ImmutableMultiset.of(op1, op2));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3) {
		return Add(ImmutableMultiset.of(op1, op2, op3));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4) {
		return Add(ImmutableMultiset.of(op1, op2, op3, op4));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4, final Expr<? extends T> op5) {
		return Add(ImmutableMultiset.of(op1, op2, op3, op4, op5));
	}

	////

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2) {
		return Mul(ImmutableMultiset.of(op1, op2));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3) {
		return Mul(ImmutableMultiset.of(op1, op2, op3));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4) {
		return Mul(ImmutableMultiset.of(op1, op2, op3, op4));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4, final Expr<? extends T> op5) {
		return Mul(ImmutableMultiset.of(op1, op2, op3, op4, op5));
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
