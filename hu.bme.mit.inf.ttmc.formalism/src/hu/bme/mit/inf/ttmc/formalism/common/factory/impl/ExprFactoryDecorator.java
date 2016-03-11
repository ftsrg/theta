package hu.bme.mit.inf.ttmc.formalism.common.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.GtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IffExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.LtExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ModExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.MulExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.OrExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;

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
	public IntLitExpr Int(long value) {
		return factory.Int(value);
	}

	@Override
	public RatLitExpr Rat(long num, long denom) {
		return factory.Rat(num, denom);
	}
	
	@Override
	public <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(ParamDecl<? super P> paramDecl,
			Expr<? extends R> result) {
		return factory.Func(paramDecl, result);
	}

	@Override
	public <P extends Type, R extends Type> FuncAppExpr<P, R> App(Expr<? extends FuncType<? super P, ? extends R>> func,
			Expr<? extends P> param) {
		return factory.App(func, param);
	}

	@Override
	public <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			Expr<? extends ArrayType<? super I, ? extends E>> array, Expr<? extends I> index) {
		return factory.Read(array, index);
	}

	@Override
	public <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			Expr<? extends ArrayType<? super I, ? extends E>> array, Expr<? extends I> index, Expr<? extends E> elem) {
		return factory.Write(array, index, elem);
	}

	@Override
	public NotExpr Not(Expr<? extends BoolType> op) {
		return factory.Not(op);
	}

	@Override
	public ImplyExpr Imply(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		return factory.Imply(leftOp, rightOp);
	}

	@Override
	public IffExpr Iff(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		return factory.Iff(leftOp, rightOp);
	}

	@Override
	public AndExpr And(Collection<? extends Expr<? extends BoolType>> ops) {
		return factory.And(ops);
	}

	@Override
	public OrExpr Or(Collection<? extends Expr<? extends BoolType>> ops) {
		return factory.Or(ops);
	}

	@Override
	public ForallExpr Forall(List<? extends ParamDecl<?>> paramDecls, Expr<? extends BoolType> op) {
		return factory.Forall(paramDecls, op);
	}

	@Override
	public ExistsExpr Exists(List<? extends ParamDecl<?>> paramDecls, Expr<? extends BoolType> op) {
		return factory.Exists(paramDecls, op);
	}

	@Override
	public EqExpr Eq(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		return factory.Eq(leftOp, rightOp);
	}

	@Override
	public NeqExpr Neq(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		return factory.Neq(leftOp, rightOp);
	}

	@Override
	public LtExpr Lt(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		return factory.Lt(leftOp, rightOp);
	}

	@Override
	public LeqExpr Leq(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		return factory.Leq(leftOp, rightOp);
	}

	@Override
	public GtExpr Gt(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		return factory.Gt(leftOp, rightOp);
	}

	@Override
	public GeqExpr Geq(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		return factory.Geq(leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderNeg> NegExpr<T> Neg(Expr<? extends T> op) {
		return factory.Neg(op);
	}

	@Override
	public <T extends ClosedUnderSub> SubExpr<T> Sub(Expr<? extends T> leftOp, Expr<? extends T> rightOp) {
		return factory.Sub(leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderAdd> AddExpr<T> Add(Collection<? extends Expr<? extends T>> ops) {
		return factory.Add(ops);
	}

	@Override
	public <T extends ClosedUnderMul> MulExpr<T> Mul(Collection<? extends Expr<? extends T>> ops) {
		return factory.Mul(ops);
	}

	@Override
	public ModExpr Mod(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		return factory.Mod(leftOp, rightOp);
	}

	@Override
	public RemExpr Rem(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		return factory.Rem(leftOp, rightOp);
	}

	@Override
	public IntDivExpr IntDiv(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		return factory.IntDiv(leftOp, rightOp);
	}

	@Override
	public RatDivExpr RatDiv(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		return factory.RatDiv(leftOp, rightOp);
	}

	@Override
	public <T extends Type> IteExpr<T> Ite(Expr<? extends BoolType> cond, Expr<? extends T> then,
			Expr<? extends T> elze) {
		return factory.Ite(cond, then, elze);
	}

}
