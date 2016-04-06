package hu.bme.mit.inf.ttmc.constraint.z3.factory;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
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
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ConstRefExpr;
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
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3IteExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3LeqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3LtExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ModExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3MulExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3NegExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3NotExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3OrExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3RemExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3SubExpr;
import hu.bme.mit.inf.ttmc.constraint.z3.expr.Z3TrueExpr;

public final class Z3ExprFactory implements ExprFactory {

	private final ConstraintManager manager;

	private final Context context;

	private final TrueExpr trueExpr;
	private final FalseExpr falseExpr;

	public Z3ExprFactory(final ConstraintManager manager, final Context context) {
		checkNotNull(context);

		this.manager = manager;

		this.context = context;

		trueExpr = new Z3TrueExpr(manager, context);
		falseExpr = new Z3FalseExpr(manager, context);
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
		return new Z3IntLitExpr(manager, value, context);
	}

	@Override
	public RatLitExpr Rat(final long num, final long denom) {
		checkArgument(denom != 0);
		return new Z3RatLitExpr(manager, num, denom, context);
	}

	@Override
	public <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(
			final ParamDecl<? super P> paramDecl, final Expr<? extends R> result) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <T extends Type> ConstRefExpr<T> Ref(final ConstDecl<T> constDecl) {
		checkNotNull(constDecl);
		return new Z3ConstRefExpr<>(manager, constDecl, context);
	}

	@Override
	public <T extends Type> ParamRefExpr<T> Ref(final ParamDecl<T> paramDecl) {
		checkNotNull(paramDecl);
		return new Z3ParamRefExpr<>(manager, paramDecl, context);
	}

	@Override
	public <P extends Type, R extends Type> FuncAppExpr<P, R> App(
			final Expr<? extends FuncType<? super P, ? extends R>> func, final Expr<? extends P> param) {
		checkNotNull(func);
		checkNotNull(param);
		return new Z3FuncAppExpr<>(manager, func, param, context);
	}

	@Override
	public <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index) {
		checkNotNull(array);
		checkNotNull(index);
		return new Z3ArrayReadExpr<>(manager, array, index, context);
	}

	@Override
	public <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index,
			final Expr<? extends E> elem) {
		checkNotNull(array);
		checkNotNull(index);
		checkNotNull(elem);
		return new Z3ArrayWriteExpr<>(manager, array, index, elem, context);
	}

	@Override
	public NotExpr Not(final Expr<? extends BoolType> op) {
		checkNotNull(op);
		return new Z3NotExpr(manager, op, context);
	}

	@Override
	public ImplyExpr Imply(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3ImplyExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public IffExpr Iff(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3IffExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public AndExpr And(final Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new Z3AndExpr(manager, ops, context);
	}

	@Override
	public OrExpr Or(final Collection<? extends Expr<? extends BoolType>> ops) {
		checkNotNull(ops);
		return new Z3OrExpr(manager, ops, context);
	}

	@Override
	public ForallExpr Forall(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new Z3ForallExpr(manager, paramDecls, op, context);
	}

	@Override
	public ExistsExpr Exists(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op) {
		checkNotNull(paramDecls);
		checkNotNull(op);
		return new Z3ExistsExpr(manager, paramDecls, op, context);
	}

	@Override
	public EqExpr Eq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3EqExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public NeqExpr Neq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3NeqExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public LtExpr Lt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3LtExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public LeqExpr Leq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3LeqExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public GtExpr Gt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3GtExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public GeqExpr Geq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3GeqExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public <T extends ClosedUnderNeg> NegExpr<T> Neg(final Expr<? extends T> op) {
		checkNotNull(op);
		return new Z3NegExpr<>(manager, op, context);
	}

	@Override
	public <T extends ClosedUnderSub> SubExpr<T> Sub(final Expr<? extends T> leftOp, final Expr<? extends T> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3SubExpr<>(manager, leftOp, rightOp, context);
	}

	@Override
	public <T extends ClosedUnderAdd> AddExpr<T> Add(final Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new Z3AddExpr<>(manager, ops, context);
	}

	@Override
	public <T extends ClosedUnderMul> MulExpr<T> Mul(final Collection<? extends Expr<? extends T>> ops) {
		checkNotNull(ops);
		return new Z3MulExpr<>(manager, ops, context);
	}

	@Override
	public ModExpr Mod(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3ModExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public RemExpr Rem(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3RemExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public IntDivExpr IntDiv(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3IntDivExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		checkNotNull(leftOp);
		checkNotNull(rightOp);
		return new Z3RatDivExpr(manager, leftOp, rightOp, context);
	}

	@Override
	public <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new Z3IteExpr<>(manager, cond, then, elze, context);
	}

}
