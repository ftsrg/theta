package hu.bme.mit.inf.ttmc.constraint.factory.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
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
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleProjExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.AddExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.AndExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ArrayReadExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ArrayWriteExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ConstRefExprImpl;
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
import hu.bme.mit.inf.ttmc.constraint.expr.impl.ParamRefExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.RatDivExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.RatLitExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.RemExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.SubExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.TrueExprImpl;
import hu.bme.mit.inf.ttmc.constraint.expr.impl.TupleProjExprImpl;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.TupleType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;

public class ExprFactoryImpl implements ExprFactory {

	private final TrueExpr trueExpr;
	private final FalseExpr falseExpr;
	
	public ExprFactoryImpl() {
		trueExpr = new TrueExprImpl();
		falseExpr = new FalseExprImpl();
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
	public IntLitExpr Int(long value) {
		return new IntLitExprImpl(value);
	}

	@Override
	public RatLitExpr Rat(long num, long denom) {
		checkArgument(denom != 0);
		return new RatLitExprImpl(num, denom);
	}

	@Override
	public TupleLitExpr Tuple(List<? extends Expr<?>> elems) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(ParamDecl<? super P> paramDecl,
			Expr<? extends R> result) {
		checkNotNull(paramDecl);
		checkNotNull(result);
		return new FuncLitExprImpl<P, R>(paramDecl, result);
	}

	@Override
	public <T extends Type> ConstRefExpr<T> Ref(ConstDecl<T> constDecl) {
		checkNotNull(constDecl);
		return new ConstRefExprImpl<T>(constDecl);
	}

	@Override
	public <T extends Type> ParamRefExpr<T> Ref(ParamDecl<T> paramDecl) {
		checkNotNull(paramDecl);
		return new ParamRefExprImpl<T>(paramDecl);
	}

	@Override
	public TupleProjExpr Proj(Expr<? extends TupleType> tup, int index) {
		checkNotNull(tup);
		checkArgument(index > 0);
		return new TupleProjExprImpl(tup, index);
	}

	@Override
	public <P extends Type, R extends Type> FuncAppExpr<P, R> App(Expr<? extends FuncType<? super P, ? extends R>> func,
			Expr<? extends P> param) {
		checkNotNull(func);
		checkNotNull(param);
		return new FuncAppExprImpl<P, R>(func, param);
	}

	@Override
	public <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			Expr<? extends ArrayType<? super I, ? extends E>> array, Expr<? extends I> index) {
		checkNotNull(array);
		checkNotNull(index);
		return new ArrayReadExprImpl<>(array, index);
	}

	@Override
	public <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			Expr<? extends ArrayType<? super I, ? extends E>> array, Expr<? extends I> index, Expr<? extends E> elem) {
		checkNotNull(array);
		checkNotNull(index);
		checkNotNull(elem);
		return new ArrayWriteExprImpl<>(array, index, elem);
	}

	@Override
	public NotExpr Not(Expr<? extends BoolType> op) {
		checkNotNull(op);
		return new NotExprImpl(op);
	}

	@Override
	public ImplyExpr Imply(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new ImplyExprImpl(leftOp, rightOp);
	}

	@Override
	public IffExpr Iff(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new IffExprImpl(leftOp, rightOp);
	}

	@Override
	public AndExpr And(Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new AndExprImpl(ops);
	}

	@Override
	public OrExpr Or(Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new OrExprImpl(ops);
	}

	@Override
	public ForallExpr Forall(List<? extends ParamDecl<?>> paramDecls, Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new ForallExprImpl(paramDecls, op);
	}

	@Override
	public ExistsExpr Exists(List<? extends ParamDecl<?>> paramDecls, Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new ExistsExprImpl(paramDecls, op);
	}

	@Override
	public EqExpr Eq(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new EqExprImpl(leftOp, rightOp);
	}

	@Override
	public NeqExpr Neq(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new NeqExprImpl(leftOp, rightOp);
	}

	@Override
	public LtExpr Lt(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new LtExprImpl(leftOp, rightOp);
	}

	@Override
	public LeqExpr Leq(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new LeqExprImpl(leftOp, rightOp);
	}

	@Override
	public GtExpr Gt(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new GtExprImpl(leftOp, rightOp);
	}

	@Override
	public GeqExpr Geq(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new GeqExprImpl(leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderNeg> NegExpr<T> Neg(Expr<? extends T> op) {
		checkNotNull(op);
		return new NegExprImpl<T>(op);
	}

	@Override
	public <T extends ClosedUnderSub> SubExpr<T> Sub(Expr<? extends T> leftOp, Expr<? extends T> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new SubExprImpl<T>(leftOp, rightOp);
	}

	@Override
	public <T extends ClosedUnderAdd> AddExpr<T> Add(Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new AddExprImpl<T>(ops);
	}

	@Override
	public <T extends ClosedUnderMul> MulExpr<T> Mul(Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new MulExprImpl<>(ops);
	}

	@Override
	public ModExpr Mod(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new ModExprImpl(leftOp, rightOp);
	}

	@Override
	public RemExpr Rem(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new RemExprImpl(leftOp, rightOp);
	}

	@Override
	public IntDivExpr IntDiv(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new IntDivExprImpl(leftOp, rightOp);
	}

	@Override
	public RatDivExpr RatDiv(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new RatDivExprImpl(leftOp, rightOp);
	}

	@Override
	public <T extends Type> IteExpr<T> Ite(Expr<? extends BoolType> cond, Expr<? extends T> then,
			Expr<? extends T> elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IteExprImpl<>(cond, then, elze);
	}

}
