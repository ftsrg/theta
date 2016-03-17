package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
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
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ExprCNFCheckerVisitor.CNFStatus;

public class ExprCNFCheckerVisitor implements ExprVisitor<CNFStatus, Boolean> {
	
	public enum CNFStatus {
		START(0), INSIDE_AND(1), INSIDE_OR(2), INSIDE_NOT(3);
		private final int value;
	    private CNFStatus(int value) { this.value = value; }
	    public int getValue() { return value; }
	}

	@Override
	public <DeclType extends Type> Boolean visit(ConstRefExpr<DeclType> expr, CNFStatus param) {
		return true;
	}

	@Override
	public <DeclType extends Type> Boolean visit(ParamRefExpr<DeclType> expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(FalseExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(TrueExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(NotExpr expr, CNFStatus param) {
		// NOT is not allowed inside NOT
		if(param.getValue() >= CNFStatus.INSIDE_NOT.getValue()) return false;
		else return expr.getOp().accept(this, CNFStatus.INSIDE_NOT);
	}

	@Override
	public Boolean visit(ImplyExpr expr, CNFStatus param) {
		return false;
	}

	@Override
	public Boolean visit(IffExpr expr, CNFStatus param) {
		return false;
	}

	@Override
	public Boolean visit(AndExpr expr, CNFStatus param) {
		// AND is allowed inside AND
		if(param.getValue() > CNFStatus.INSIDE_AND.getValue()) return false;
		else return expr.getOps().stream().allMatch(op -> op.accept(this, CNFStatus.INSIDE_AND));
	}

	@Override
	public Boolean visit(OrExpr expr, CNFStatus param) {
		// OR is allowed inside OR
		if(param.getValue() > CNFStatus.INSIDE_OR.getValue()) return false;
		else return expr.getOps().stream().allMatch(op -> op.accept(this, CNFStatus.INSIDE_OR));
	}

	@Override
	public Boolean visit(ExistsExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(ForallExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(EqExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(NeqExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(GeqExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(GtExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(LeqExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(LtExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(IntLitExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(IntDivExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(RemExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(ModExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(RatLitExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(RatDivExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Boolean visit(NegExpr<ExprType> expr, CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderSub> Boolean visit(SubExpr<ExprType> expr, CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Boolean visit(AddExpr<ExprType> expr, CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderMul> Boolean visit(MulExpr<ExprType> expr, CNFStatus param) {
		return true;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Boolean visit(ArrayReadExpr<IndexType, ElemType> expr,
			CNFStatus param) {
		return true;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Boolean visit(ArrayWriteExpr<IndexType, ElemType> expr,
			CNFStatus param) {
		return true;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Boolean visit(FuncLitExpr<ParamType, ResultType> expr,
			CNFStatus param) {
		return true;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Boolean visit(FuncAppExpr<ParamType, ResultType> expr,
			CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(TupleLitExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(TupleProjExpr expr, CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends Type> Boolean visit(IteExpr<ExprType> expr, CNFStatus param) {
		return false;
	}
}
