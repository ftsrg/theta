package hu.bme.mit.inf.ttmc.constraint.factory.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
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
import hu.bme.mit.inf.ttmc.constraint.expr.impl.AddExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.AndExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ArrayReadExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ArrayWriteExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.EqExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ExistsExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.FalseExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ForallExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.FuncAppExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.FuncLitExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.GeqExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.GtExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.IffExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ImplyExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.IntDivExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.IntLitExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.IteExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.LeqExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.LtExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ModExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.MulExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.NegExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.NeqExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.NotExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.OrExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.RatDivExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.RatLitExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.RemExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.SubExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.TrueExprImpl;
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

public class ExprFactoryImpl implements ExprFactory {

	private final ConstraintManager manager;

	private final TrueExpr trueExpr;
	private final FalseExpr falseExpr;

	public ExprFactoryImpl(final ConstraintManager manager) {
		this.manager = manager;
		trueExpr = new TrueExprImpl(manager);
		falseExpr = new FalseExprImpl(manager);
	}

	@Override
	public TrueExpr True() {
		return trueExpr;
	}

	@Override
	public FalseExpr False() {
		return falseExpr;
	}

	@Override
	public IntLitExpr Int(final long value) {
		return new IntLitExprImpl(manager, value);
	}

	@Override
	public RatLitExpr Rat(final long num, final long denom) {
		checkArgument(denom != 0);
		return new RatLitExprImpl(manager, num, denom);
	}

	@Override
	public <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(
			final ParamDecl<? super P> paramDecl, final Expr<? extends R> result) {
		checkNotNull(paramDecl);
		checkNotNull(result);
		return new FuncLitExprImpl<P, R>(manager, paramDecl, result);
	}

	@Override
	public <P extends Type, R extends Type> FuncAppExpr<P, R> App(
			final Expr<? extends FuncType<? super P, ? extends R>> func, final Expr<? extends P> param) {
		checkNotNull(func);
		checkNotNull(param);
		return new FuncAppExprImpl<P, R>(manager, func, param);
	}

	@Override
	public <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index) {
		checkNotNull(array);
		checkNotNull(index);
		return new ArrayReadExprImpl<>(manager, array, index);
	}

	@Override
	public <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index,
			final Expr<? extends E> elem) {
		checkNotNull(array);
		checkNotNull(index);
		checkNotNull(elem);
		return new ArrayWriteExprImpl<>(manager, array, index, elem);
	}

	@Override
	public NotExpr Not(final Expr<? extends BoolType> op) {
		checkNotNull(op);
		return new NotExprImpl(manager, op);
	}

	@Override
	public ImplyExpr Imply(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new ImplyExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public IffExpr Iff(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new IffExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public AndExpr And(final Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new AndExprImpl(manager, ops);
	}

	@Override
	public OrExpr Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new OrExprImpl(manager, ops);
	}

	@Override
	public ForallExpr Forall(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new ForallExprImpl(manager, paramDecls, op);
	}

	@Override
	public ExistsExpr Exists(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new ExistsExprImpl(manager, paramDecls, op);
	}

	@Override
	public EqExpr Eq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new EqExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public NeqExpr Neq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new NeqExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public LtExpr Lt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new LtExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public LeqExpr Leq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new LeqExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public GtExpr Gt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new GtExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public GeqExpr Geq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new GeqExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderNeg> NegExpr<T> Neg(final Expr<? extends T> op) {
		checkNotNull(op);
		return new NegExprImpl<T>(manager, op);
	}

	@Override
	public <T extends ClosedUnderSub> SubExpr<T> Sub(final Expr<? extends T> leftOp, final Expr<? extends T> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new SubExprImpl<T>(manager, leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderAdd> AddExpr<T> Add(final Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new AddExprImpl<T>(manager, ops);
	}

	@Override
	public <T extends ClosedUnderMul> MulExpr<T> Mul(final Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new MulExprImpl<>(manager, ops);
	}

	@Override
	public ModExpr Mod(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new ModExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public RemExpr Rem(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new RemExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public IntDivExpr IntDiv(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new IntDivExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new RatDivExprImpl(manager, leftOp, rightOp);
	}

	@Override
	public <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IteExprImpl<>(manager, cond, then, elze);
	}

}
