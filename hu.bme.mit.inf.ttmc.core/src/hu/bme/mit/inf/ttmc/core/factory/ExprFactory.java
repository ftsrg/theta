package hu.bme.mit.inf.ttmc.core.factory;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.BoolLitExpr;
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
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
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

public interface ExprFactory {

	public TrueExpr True();

	public FalseExpr False();

	public default BoolLitExpr Bool(final boolean value) {
		if (value) {
			return True();
		} else {
			return False();
		}
	}

	public IntLitExpr Int(final long value);

	public RatLitExpr Rat(final long num, final long denom);

	public <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(
			final ParamDecl<? super P> paramDecl, final Expr<? extends R> result);

	// LHS

	public <P extends Type, R extends Type> FuncAppExpr<P, R> App(
			final Expr<? extends FuncType<? super P, ? extends R>> func, final Expr<? extends P> param);

	public <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index);

	//

	public <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index,
			final Expr<? extends E> elem);

	// Boolean connectives

	public NotExpr Not(final Expr<? extends BoolType> op);

	public ImplyExpr Imply(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp);

	public IffExpr Iff(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp);

	public AndExpr And(final Collection<? extends Expr<? extends BoolType>> ops);

	@SuppressWarnings("unchecked")
	public default AndExpr And(final Expr<? extends BoolType>... ops) {
		return And(ImmutableSet.copyOf(ops));
	}

	public OrExpr Or(final Collection<? extends Expr<? extends BoolType>> ops);

	@SuppressWarnings("unchecked")
	public default OrExpr Or(final Expr<? extends BoolType>... ops) {
		return Or(ImmutableSet.copyOf(ops));
	}

	// Quantifiers

	public ForallExpr Forall(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op);

	public ExistsExpr Exists(final List<? extends ParamDecl<?>> paramDecls, final Expr<? extends BoolType> op);

	// Equality

	public EqExpr Eq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp);

	public NeqExpr Neq(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp);

	// Order

	public LtExpr Lt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	public LeqExpr Leq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	public GtExpr Gt(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	public GeqExpr Geq(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	// Arithmetic

	public <T extends ClosedUnderNeg> NegExpr<T> Neg(final Expr<? extends T> op);

	public <T extends ClosedUnderSub> SubExpr<T> Sub(final Expr<? extends T> leftOp, final Expr<? extends T> rightOp);

	public <T extends ClosedUnderAdd> AddExpr<T> Add(final Collection<? extends Expr<? extends T>> ops);

	@SuppressWarnings("unchecked")
	public default <T extends ClosedUnderAdd> AddExpr<T> Add(final Expr<? extends T>... ops) {
		return Add(ImmutableMultiset.copyOf(ops));
	}

	public <T extends ClosedUnderMul> MulExpr<T> Mul(final Collection<? extends Expr<? extends T>> ops);

	@SuppressWarnings("unchecked")
	public default <T extends ClosedUnderMul> MulExpr<T> Mul(final Expr<? extends T>... ops) {
		return Mul(ImmutableMultiset.copyOf(ops));
	}

	public ModExpr Mod(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	public RemExpr Rem(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	public IntDivExpr IntDiv(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	public RatDivExpr RatDiv(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	// if-then-else

	public <T extends Type> IteExpr<T> Ite(final Expr<? extends BoolType> cond, final Expr<? extends T> then,
			final Expr<? extends T> elze);
}
