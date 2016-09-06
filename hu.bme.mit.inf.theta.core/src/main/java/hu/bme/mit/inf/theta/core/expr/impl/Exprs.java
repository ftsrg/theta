package hu.bme.mit.inf.theta.core.expr.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.expr.AddExpr;
import hu.bme.mit.inf.theta.core.expr.AndExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.theta.core.expr.BoolLitExpr;
import hu.bme.mit.inf.theta.core.expr.EqExpr;
import hu.bme.mit.inf.theta.core.expr.ExistsExpr;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.FalseExpr;
import hu.bme.mit.inf.theta.core.expr.ForallExpr;
import hu.bme.mit.inf.theta.core.expr.FuncAppExpr;
import hu.bme.mit.inf.theta.core.expr.FuncLitExpr;
import hu.bme.mit.inf.theta.core.expr.GeqExpr;
import hu.bme.mit.inf.theta.core.expr.GtExpr;
import hu.bme.mit.inf.theta.core.expr.IffExpr;
import hu.bme.mit.inf.theta.core.expr.ImplyExpr;
import hu.bme.mit.inf.theta.core.expr.IntDivExpr;
import hu.bme.mit.inf.theta.core.expr.IntLitExpr;
import hu.bme.mit.inf.theta.core.expr.IteExpr;
import hu.bme.mit.inf.theta.core.expr.LeqExpr;
import hu.bme.mit.inf.theta.core.expr.LtExpr;
import hu.bme.mit.inf.theta.core.expr.ModExpr;
import hu.bme.mit.inf.theta.core.expr.MulExpr;
import hu.bme.mit.inf.theta.core.expr.NegExpr;
import hu.bme.mit.inf.theta.core.expr.NeqExpr;
import hu.bme.mit.inf.theta.core.expr.NotExpr;
import hu.bme.mit.inf.theta.core.expr.OrExpr;
import hu.bme.mit.inf.theta.core.expr.RatDivExpr;
import hu.bme.mit.inf.theta.core.expr.RatLitExpr;
import hu.bme.mit.inf.theta.core.expr.RemExpr;
import hu.bme.mit.inf.theta.core.expr.SubExpr;
import hu.bme.mit.inf.theta.core.expr.TrueExpr;
import hu.bme.mit.inf.theta.core.type.ArrayType;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.FuncType;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderSub;

public final class Exprs {

	private static final TrueExpr TRUE_EXPR;
	private static final FalseExpr FALSE_EXPR;

	static {
		TRUE_EXPR = new TrueExprImpl();
		FALSE_EXPR = new FalseExprImpl();
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

	public static IntLitExpr Int(final long value) {
		return new IntLitExprImpl(value);
	}

	public static RatLitExpr Rat(final long num, final long denom) {
		checkArgument(denom != 0);
		return new RatLitExprImpl(num, denom);
	}

	public static <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(
			final ParamDecl<? super P> paramDecl, final Expr<? extends R> result) {
		checkNotNull(paramDecl);
		checkNotNull(result);
		return new FuncLitExprImpl<P, R>(paramDecl, result);
	}

	public static <P extends Type, R extends Type> FuncAppExpr<P, R> App(
			final Expr<? extends FuncType<? super P, ? extends R>> func, final Expr<? extends P> param) {
		checkNotNull(func);
		checkNotNull(param);
		return new FuncAppExprImpl<P, R>(func, param);
	}

	public static <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index) {
		checkNotNull(array);
		checkNotNull(index);
		return new ArrayReadExprImpl<>(array, index);
	}

	public static <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index,
			final Expr<? extends E> elem) {
		checkNotNull(array);
		checkNotNull(index);
		checkNotNull(elem);
		return new ArrayWriteExprImpl<>(array, index, elem);
	}

	public static NotExpr Not(final Expr<? extends BoolType> op) {
		checkNotNull(op);
		return new NotExprImpl(op);
	}

	public static ImplyExpr Imply(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new ImplyExprImpl(leftOp, rightOp);
	}

	public static IffExpr Iff(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new IffExprImpl(leftOp, rightOp);
	}

	public static AndExpr And(final Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new AndExprImpl(ops);
	}

	public static OrExpr Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new OrExprImpl(ops);
	}

	public static ForallExpr Forall(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new ForallExprImpl(paramDecls, op);
	}

	public static ExistsExpr Exists(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new ExistsExprImpl(paramDecls, op);
	}

	public static EqExpr Eq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new EqExprImpl(leftOp, rightOp);
	}

	public static NeqExpr Neq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new NeqExprImpl(leftOp, rightOp);
	}

	public static LtExpr Lt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new LtExprImpl(leftOp, rightOp);
	}

	public static LeqExpr Leq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new LeqExprImpl(leftOp, rightOp);
	}

	public static GtExpr Gt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new GtExprImpl(leftOp, rightOp);
	}

	public static GeqExpr Geq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new GeqExprImpl(leftOp, rightOp);
	}

	public static <T extends ClosedUnderNeg> NegExpr<T> Neg(final Expr<? extends T> op) {
		checkNotNull(op);
		return new NegExprImpl<T>(op);
	}

	public static <T extends ClosedUnderSub> SubExpr<T> Sub(final Expr<? extends T> leftOp,
			final Expr<? extends T> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new SubExprImpl<T>(leftOp, rightOp);
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new AddExprImpl<T>(ops);
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new MulExprImpl<>(ops);
	}

	public static ModExpr Mod(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new ModExprImpl(leftOp, rightOp);
	}

	public static RemExpr Rem(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new RemExprImpl(leftOp, rightOp);
	}

	public static IntDivExpr IntDiv(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new IntDivExprImpl(leftOp, rightOp);
	}

	public static RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new RatDivExprImpl(leftOp, rightOp);
	}

	public static <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IteExprImpl<>(cond, then, elze);
	}

	/*
	 * Convenience methods
	 */

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		checkNotNull(op1);
		checkNotNull(op2);
		return And(ImmutableSet.of(op1, op2));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		return And(ImmutableSet.of(op1, op2, op3));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		return And(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static AndExpr And(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		checkNotNull(op5);
		return And(ImmutableSet.of(op1, op2, op3, op4, op5));
	}

	////

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2) {
		checkNotNull(op1);
		checkNotNull(op2);
		return Or(ImmutableSet.of(op1, op2));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		return Or(ImmutableSet.of(op1, op2, op3));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		return Or(ImmutableSet.of(op1, op2, op3, op4));
	}

	public static OrExpr Or(final Expr<? extends BoolType> op1, final Expr<? extends BoolType> op2,
			final Expr<? extends BoolType> op3, final Expr<? extends BoolType> op4,
			final Expr<? extends BoolType> op5) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		checkNotNull(op5);
		return Or(ImmutableSet.of(op1, op2, op3, op4, op5));
	}

	////

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2) {
		checkNotNull(op1);
		checkNotNull(op2);
		return Add(ImmutableMultiset.of(op1, op2));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		return Add(ImmutableMultiset.of(op1, op2, op3));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		return Add(ImmutableMultiset.of(op1, op2, op3, op4));
	}

	public static <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4, final Expr<? extends T> op5) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		checkNotNull(op5);
		return Add(ImmutableMultiset.of(op1, op2, op3, op4, op5));
	}

	////

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2) {
		checkNotNull(op1);
		checkNotNull(op2);
		return Mul(ImmutableMultiset.of(op1, op2));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		return Mul(ImmutableMultiset.of(op1, op2, op3));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		return Mul(ImmutableMultiset.of(op1, op2, op3, op4));
	}

	public static <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T> op1, final Expr<? extends T> op2,
			final Expr<? extends T> op3, final Expr<? extends T> op4, final Expr<? extends T> op5) {
		checkNotNull(op1);
		checkNotNull(op2);
		checkNotNull(op3);
		checkNotNull(op4);
		checkNotNull(op5);
		return Mul(ImmutableMultiset.of(op1, op2, op3, op4, op5));
	}

}
