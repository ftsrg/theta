package hu.bme.mit.inf.ttmc.formalism.sts.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.core.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IffExpr;
import hu.bme.mit.inf.ttmc.core.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.IteExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.ModExpr;
import hu.bme.mit.inf.ttmc.core.expr.MulExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.core.type.ArrayType;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.FuncType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;

public abstract class ExprFactoryDecorator implements ExprFactory {

	private final ExprFactory factory;

	public ExprFactoryDecorator(final ExprFactory factory) {
		checkNotNull(factory);
		this.factory = factory;
	}

	@Override
	public TrueExpr True() {
		return factory.True();
	}

	@Override
	public FalseExpr False() {
		return factory.False();
	}

	@Override
	public IntLitExpr Int(final long value) {
		return factory.Int(value);
	}

	@Override
	public RatLitExpr Rat(final long num, final long denom) {
		return factory.Rat(num, denom);
	}

	@Override
	public <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(
			final ParamDecl<? super P> paramDecl, final Expr<? extends R> result) {
		return factory.Func(paramDecl, result);
	}

	@Override
	public <T extends Type> ConstRefExpr<T> Ref(final ConstDecl<T> constDecl) {
		return factory.Ref(constDecl);
	}

	@Override
	public <T extends Type> ParamRefExpr<T> Ref(final ParamDecl<T> paramDecl) {
		return factory.Ref(paramDecl);
	}

	@Override
	public <P extends Type, R extends Type> FuncAppExpr<P, R> App(
			final Expr<? extends FuncType<? super P, ? extends R>> func, final Expr<? extends P> param) {
		return factory.App(func, param);
	}

	@Override
	public <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index) {
		return factory.Read(array, index);
	}

	@Override
	public <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index,
			final Expr<? extends E> elem) {
		return factory.Write(array, index, elem);
	}

	@Override
	public NotExpr Not(final Expr<? extends BoolType> op) {
		return factory.Not(op);
	}

	@Override
	public ImplyExpr Imply(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		return factory.Imply(leftOp, rightOp);
	}

	@Override
	public IffExpr Iff(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		return factory.Iff(leftOp, rightOp);
	}

	@Override
	public AndExpr And(final Collection<? extends Expr<? extends BoolType>> ops) {
		return factory.And(ops);
	}

	@Override
	public OrExpr Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		return factory.Or(ops);
	}

	@Override
	public ForallExpr Forall(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		return factory.Forall(paramDecls, op);
	}

	@Override
	public ExistsExpr Exists(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		return factory.Exists(paramDecls, op);
	}

	@Override
	public EqExpr Eq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		return factory.Eq(leftOp, rightOp);
	}

	@Override
	public NeqExpr Neq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		return factory.Neq(leftOp, rightOp);
	}

	@Override
	public LtExpr Lt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return factory.Lt(leftOp, rightOp);
	}

	@Override
	public LeqExpr Leq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return factory.Leq(leftOp, rightOp);
	}

	@Override
	public GtExpr Gt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return factory.Gt(leftOp, rightOp);
	}

	@Override
	public GeqExpr Geq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return factory.Geq(leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderNeg> NegExpr<T> Neg(final Expr<? extends T> op) {
		return factory.Neg(op);
	}

	@Override
	public <T extends ClosedUnderSub> SubExpr<T> Sub(final Expr<? extends T> leftOp, final Expr<? extends T> rightOp) {
		return factory.Sub(leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderAdd> AddExpr<T> Add(final Collection<? extends Expr<? extends T>> ops) {
		return factory.Add(ops);
	}

	@Override
	public <T extends ClosedUnderMul> MulExpr<T> Mul(final Collection<? extends Expr<? extends T>> ops) {
		return factory.Mul(ops);
	}

	@Override
	public ModExpr Mod(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return factory.Mod(leftOp, rightOp);
	}

	@Override
	public RemExpr Rem(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return factory.Rem(leftOp, rightOp);
	}

	@Override
	public IntDivExpr IntDiv(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		return factory.IntDiv(leftOp, rightOp);
	}

	@Override
	public RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		return factory.RatDiv(leftOp, rightOp);
	}

	@Override
	public <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze) {
		return factory.Ite(cond, then, elze);
	}

}
