package hu.bme.mit.inf.theta.core.utils.impl;

import hu.bme.mit.inf.theta.core.expr.AddExpr;
import hu.bme.mit.inf.theta.core.expr.AndExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.theta.core.expr.ConstRefExpr;
import hu.bme.mit.inf.theta.core.expr.EqExpr;
import hu.bme.mit.inf.theta.core.expr.ExistsExpr;
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
import hu.bme.mit.inf.theta.core.expr.ParamRefExpr;
import hu.bme.mit.inf.theta.core.expr.RatDivExpr;
import hu.bme.mit.inf.theta.core.expr.RatLitExpr;
import hu.bme.mit.inf.theta.core.expr.RemExpr;
import hu.bme.mit.inf.theta.core.expr.SubExpr;
import hu.bme.mit.inf.theta.core.expr.TrueExpr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;

public class IsBoolConnExprVisitor implements ExprVisitor<Void, Boolean> {

	@Override
	public <DeclType extends Type> Boolean visit(ConstRefExpr<DeclType> expr, Void param) {
		return false;
	}

	@Override
	public <DeclType extends Type> Boolean visit(ParamRefExpr<DeclType> expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(FalseExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(TrueExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(NotExpr expr, Void param) {
		return true;
	}

	@Override
	public Boolean visit(ImplyExpr expr, Void param) {
		return true;
	}

	@Override
	public Boolean visit(IffExpr expr, Void param) {
		return true;
	}

	@Override
	public Boolean visit(AndExpr expr, Void param) {
		return true;
	}

	@Override
	public Boolean visit(OrExpr expr, Void param) {
		return true;
	}

	@Override
	public Boolean visit(ExistsExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(ForallExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(EqExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(NeqExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(GeqExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(GtExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(LeqExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(LtExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(IntLitExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(IntDivExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(RemExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(ModExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(RatLitExpr expr, Void param) {
		return false;
	}

	@Override
	public Boolean visit(RatDivExpr expr, Void param) {
		return false;
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Boolean visit(NegExpr<ExprType> expr, Void param) {
		return false;
	}

	@Override
	public <ExprType extends ClosedUnderSub> Boolean visit(SubExpr<ExprType> expr, Void param) {
		return false;
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Boolean visit(AddExpr<ExprType> expr, Void param) {
		return false;
	}

	@Override
	public <ExprType extends ClosedUnderMul> Boolean visit(MulExpr<ExprType> expr, Void param) {
		return false;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Boolean visit(ArrayReadExpr<IndexType, ElemType> expr,
			Void param) {
		return false;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Boolean visit(ArrayWriteExpr<IndexType, ElemType> expr,
			Void param) {
		return false;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Boolean visit(FuncLitExpr<ParamType, ResultType> expr,
			Void param) {
		return false;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Boolean visit(FuncAppExpr<ParamType, ResultType> expr,
			Void param) {
		return false;
	}

	@Override
	public <ExprType extends Type> Boolean visit(IteExpr<ExprType> expr, Void param) {
		return false;
	}

}
