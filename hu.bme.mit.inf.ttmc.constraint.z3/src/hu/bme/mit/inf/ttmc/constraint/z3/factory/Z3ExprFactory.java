package hu.bme.mit.inf.ttmc.constraint.z3.factory;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import com.microsoft.z3.Context;

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
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3AddExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3AndExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3EqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ExistsExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3FalseExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ForallExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3GeqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3GtExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3IffExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3IntDivExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3IntLitExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3LtExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ModExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3MulExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3NegExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3NotExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3OrExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3RemExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3SubExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3TrueExpr;

public final class Z3ExprFactory implements ExprFactory {

	private final Context context;

	private final TrueExpr trueExpr;
	private final FalseExpr falseExpr;

	public Z3ExprFactory(final Context context) {
		checkNotNull(context);

		this.context = context;

		trueExpr = new Z3TrueExpr(context);
		falseExpr = new Z3FalseExpr(context);
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
		return new Z3IntLitExpr(value, context);
	}

	@Override
	public RatLitExpr Rat(long num, long denom) {
		checkArgument(denom != 0);
		return new Z3RatLitExpr(num, denom, context);
	}

	@Override
	public <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(ParamDecl<? super P> paramDecl,
			Expr<? extends R> result) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <P extends Type, R extends Type> FuncAppExpr<P, R> App(Expr<? extends FuncType<? super P, ? extends R>> func,
			Expr<? extends P> param) {
		checkNotNull(func);
		checkNotNull(param);
		return new Z3FuncAppExpr<>(func, param, context);
	}
	
	@Override
	public <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			Expr<? extends ArrayType<? super I, ? extends E>> array, Expr<? extends I> index) {
		checkNotNull(array);
		checkNotNull(index);
		return new Z3ArrayReadExpr<>(array, index, context);
	}

	@Override
	public <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			Expr<? extends ArrayType<? super I, ? extends E>> array, Expr<? extends I> index, Expr<? extends E> elem) {
		checkNotNull(array);
		checkNotNull(index);
		checkNotNull(elem);
		return new Z3ArrayWriteExpr<>(array, index, elem, context);
	}

	@Override
	public NotExpr Not(Expr<? extends BoolType> op) {
		checkNotNull(op);
		return new Z3NotExpr(op, context);
	}

	@Override
	public ImplyExpr Imply(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3ImplyExpr(leftOp, rightOp, context);
	}

	@Override
	public IffExpr Iff(Expr<? extends BoolType> leftOp, Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3IffExpr(leftOp, rightOp, context);
	}

	@Override
	public AndExpr And(Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new Z3AndExpr(ops, context);
	}

	@Override
	public OrExpr Or(Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new Z3OrExpr(ops, context);
	}

	@Override
	public ForallExpr Forall(List<? extends ParamDecl<?>> paramDecls, Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new Z3ForallExpr(paramDecls, op, context);
	}

	@Override
	public ExistsExpr Exists(List<? extends ParamDecl<?>> paramDecls, Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new Z3ExistsExpr(paramDecls, op, context);
	}

	@Override
	public EqExpr Eq(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3EqExpr(leftOp, rightOp, context);
	}

	@Override
	public NeqExpr Neq(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3NeqExpr(leftOp, rightOp, context);
	}

	@Override
	public LtExpr Lt(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3LtExpr(leftOp, rightOp, context);
	}

	@Override
	public LeqExpr Leq(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3LeqExpr(leftOp, rightOp, context);
	}

	@Override
	public GtExpr Gt(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3GtExpr(leftOp, rightOp, context);
	}

	@Override
	public GeqExpr Geq(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3GeqExpr(leftOp, rightOp, context);
	}

	@Override
	public <T extends ClosedUnderNeg> NegExpr<T> Neg(Expr<? extends T> op) {
		checkNotNull(op);
		return new Z3NegExpr<>(op, context);
	}

	@Override
	public <T extends ClosedUnderSub> SubExpr<T> Sub(Expr<? extends T> leftOp, Expr<? extends T> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3SubExpr<>(leftOp, rightOp, context);
	}

	@Override
	public <T extends ClosedUnderAdd> AddExpr<T> Add(Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new Z3AddExpr<>(ops, context);
	}

	@Override
	public <T extends ClosedUnderMul> MulExpr<T> Mul(Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new Z3MulExpr<>(ops, context);
	}

	@Override
	public ModExpr Mod(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3ModExpr(leftOp, rightOp, context);
	}

	@Override
	public RemExpr Rem(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3RemExpr(leftOp, rightOp, context);
	}

	@Override
	public IntDivExpr IntDiv(Expr<? extends IntType> leftOp, Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3IntDivExpr(leftOp, rightOp, context);
	}

	@Override
	public RatDivExpr RatDiv(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3RatDivExpr(leftOp, rightOp, context);
	}

	@Override
	public <T extends Type> IteExpr<T> Ite(Expr<? extends BoolType> cond, Expr<? extends T> then,
			Expr<? extends T> elze) {
		throw new UnsupportedOperationException("TODO");
	}

}
