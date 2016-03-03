package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
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
import hu.bme.mit.inf.ttmc.constraint.expr.MultiaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NegExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.OrExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.RemExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.TupleProjExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

/**
 * Arity based abstract visitor class.
 * @author Akos
 *
 * @param <P>
 * @param <R>
 */
public abstract class ArityBasedExprVisitor<P, R> implements ExprVisitor<P, R> {
	
	// Abstract methods that must be implemented
	
	protected abstract <ExprType extends Type> R visitNullary(NullaryExpr<ExprType> expr, P param);
	
	protected abstract <OpType extends Type, ExprType extends Type> R visitUnary(UnaryExpr<OpType, ExprType> expr, P param);
	
	protected abstract<LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> R visitBinary(BinaryExpr<LeftOpType, RightOpType, ExprType> expr, P param);
	
	protected abstract <OpsType extends Type, ExprType extends Type> R visitMultiary(MultiaryExpr<OpsType, ExprType> expr, P param);
	
	public abstract <IndexType extends Type, ElemType extends Type> R visit(ArrayReadExpr<IndexType, ElemType> expr, P param);

	public abstract <IndexType extends Type, ElemType extends Type> R visit(ArrayWriteExpr<IndexType, ElemType> expr, P param);

	public abstract <ParamType extends Type, ResultType extends Type> R visit(FuncLitExpr<ParamType, ResultType> expr, P param);

	public abstract <ParamType extends Type, ResultType extends Type> R visit(FuncAppExpr<ParamType, ResultType> expr, P param);

	public abstract <ExprType extends Type> R visit(IteExpr<ExprType> expr, P param);
	
	// Methods that can be reduced to the abstract methods
	
	@Override
	public <DeclType extends Type> R visit(ConstRefExpr<DeclType> expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public <DeclType extends Type> R visit(ParamRefExpr<DeclType> expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(FalseExpr expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(TrueExpr expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(NotExpr expr, P param) {
		return visitUnary(expr, param);
	}

	@Override
	public R visit(ImplyExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(IffExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(AndExpr expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public R visit(OrExpr expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public R visit(ExistsExpr expr, P param) {
		return visitUnary(expr, param);
	}

	@Override
	public R visit(ForallExpr expr, P param) {
		return visitUnary(expr, param);
	}

	@Override
	public R visit(EqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(NeqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(GeqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(GtExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(LeqExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(LtExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(IntLitExpr expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(IntDivExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(RemExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(ModExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public R visit(RatLitExpr expr, P param) {
		return visitNullary(expr, param);
	}

	@Override
	public R visit(RatDivExpr expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> R visit(NegExpr<ExprType> expr, P param) {
		return visitUnary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderSub> R visit(SubExpr<ExprType> expr, P param) {
		return visitBinary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderAdd> R visit(AddExpr<ExprType> expr, P param) {
		return visitMultiary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> R visit(MulExpr<ExprType> expr, P param) {
		return visitMultiary(expr, param);
	}


	@Override
	public R visit(TupleLitExpr expr, P param) {
		return visitMultiary(expr, param);	
	}

	@Override
	public R visit(TupleProjExpr expr, P param) {
		return visitUnary(expr, param);
	}


}
