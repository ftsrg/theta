package hu.bme.mit.inf.ttmc.core.utils.impl;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
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
import hu.bme.mit.inf.ttmc.core.expr.MultiaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;

public abstract class ArityBasedExprVisitor<P, R> implements ExprVisitor<P, R> {
	
	protected abstract <ExprType extends Type> R visitNullary(NullaryExpr<ExprType> expr, P param);
	
	protected abstract <OpType extends Type, ExprType extends Type> R visitUnary(UnaryExpr<OpType, ExprType> expr, P param);
	
	protected abstract<LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> R visitBinary(BinaryExpr<LeftOpType, RightOpType, ExprType> expr, P param);
	
	protected abstract <OpsType extends Type, ExprType extends Type> R visitMultiary(MultiaryExpr<OpsType, ExprType> expr, P param);
	
	public abstract <IndexType extends Type, ElemType extends Type> R visit(ArrayReadExpr<IndexType, ElemType> expr, P param);

	public abstract <IndexType extends Type, ElemType extends Type> R visit(ArrayWriteExpr<IndexType, ElemType> expr, P param);

	public abstract <ParamType extends Type, ResultType extends Type> R visit(FuncLitExpr<ParamType, ResultType> expr, P param);

	public abstract <ParamType extends Type, ResultType extends Type> R visit(FuncAppExpr<ParamType, ResultType> expr, P param);

	public abstract <ExprType extends Type> R visit(IteExpr<ExprType> expr, P param);
	
	/////
	
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

}
