package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.AndExpr;
import hu.bme.mit.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.ExistsExpr;
import hu.bme.mit.theta.core.expr.FalseExpr;
import hu.bme.mit.theta.core.expr.ForallExpr;
import hu.bme.mit.theta.core.expr.FuncAppExpr;
import hu.bme.mit.theta.core.expr.FuncLitExpr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.IffExpr;
import hu.bme.mit.theta.core.expr.ImplyExpr;
import hu.bme.mit.theta.core.expr.IntDivExpr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.ModExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.expr.NotExpr;
import hu.bme.mit.theta.core.expr.OrExpr;
import hu.bme.mit.theta.core.expr.ParamRefExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.ProcRefExpr;
import hu.bme.mit.theta.core.expr.RatDivExpr;
import hu.bme.mit.theta.core.expr.RatLitExpr;
import hu.bme.mit.theta.core.expr.RemExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.expr.TrueExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.core.utils.impl.CnfCheckerVisitor.CNFStatus;

final class CnfCheckerVisitor implements ExprVisitor<CNFStatus, Boolean> {

	enum CNFStatus {
		START(0), INSIDE_AND(1), INSIDE_OR(2), INSIDE_NOT(3);
		private final int value;

		private CNFStatus(final int value) {
			this.value = value;
		}

		public int getValue() {
			return value;
		}
	}

	@Override
	public <DeclType extends Type> Boolean visit(final ConstRefExpr<DeclType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <DeclType extends Type> Boolean visit(final ParamRefExpr<DeclType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <DeclType extends Type> Boolean visit(final VarRefExpr<DeclType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ReturnType extends Type> Boolean visit(final ProcRefExpr<ReturnType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends Type> Boolean visit(final PrimedExpr<ExprType> expr, final CNFStatus param) {
		return expr.getOp().accept(this, CNFStatus.INSIDE_NOT);
	}

	@Override
	public Boolean visit(final FalseExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final TrueExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final NotExpr expr, final CNFStatus param) {
		// NOT is not allowed inside NOT
		if (param.getValue() >= CNFStatus.INSIDE_NOT.getValue())
			return false;
		else
			return expr.getOp().accept(this, CNFStatus.INSIDE_NOT);
	}

	@Override
	public Boolean visit(final ImplyExpr expr, final CNFStatus param) {
		return false;
	}

	@Override
	public Boolean visit(final IffExpr expr, final CNFStatus param) {
		return false;
	}

	@Override
	public Boolean visit(final AndExpr expr, final CNFStatus param) {
		// AND is allowed inside AND
		if (param.getValue() > CNFStatus.INSIDE_AND.getValue())
			return false;
		else
			return expr.getOps().stream().allMatch(op -> op.accept(this, CNFStatus.INSIDE_AND));
	}

	@Override
	public Boolean visit(final OrExpr expr, final CNFStatus param) {
		// OR is allowed inside OR
		if (param.getValue() > CNFStatus.INSIDE_OR.getValue())
			return false;
		else
			return expr.getOps().stream().allMatch(op -> op.accept(this, CNFStatus.INSIDE_OR));
	}

	@Override
	public Boolean visit(final ExistsExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final ForallExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final EqExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final NeqExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final GeqExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final GtExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final LeqExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final LtExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final IntLitExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final IntDivExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final RemExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final ModExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final RatLitExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public Boolean visit(final RatDivExpr expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Boolean visit(final NegExpr<ExprType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderSub> Boolean visit(final SubExpr<ExprType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Boolean visit(final AddExpr<ExprType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends ClosedUnderMul> Boolean visit(final MulExpr<ExprType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Boolean visit(final ArrayReadExpr<IndexType, ElemType> expr,
			final CNFStatus param) {
		return true;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Boolean visit(final ArrayWriteExpr<IndexType, ElemType> expr,
			final CNFStatus param) {
		return true;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Boolean visit(
			final FuncLitExpr<ParamType, ResultType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Boolean visit(
			final FuncAppExpr<ParamType, ResultType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ReturnType extends Type> Boolean visit(final ProcCallExpr<ReturnType> expr, final CNFStatus param) {
		return true;
	}

	@Override
	public <ExprType extends Type> Boolean visit(final IteExpr<ExprType> expr, final CNFStatus param) {
		return false;
	}

}
