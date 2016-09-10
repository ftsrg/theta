package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.AndExpr;
import hu.bme.mit.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.ExistsExpr;
import hu.bme.mit.theta.core.expr.Expr;
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
import hu.bme.mit.theta.core.expr.RatDivExpr;
import hu.bme.mit.theta.core.expr.RatLitExpr;
import hu.bme.mit.theta.core.expr.RemExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.expr.TrueExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public class ExprCnfChecker {
	
	private ExprCNFVisitor visitor;
	
	public ExprCnfChecker() {
		this(new ExprCNFVisitor());
	}
	
	// Derived classes can call this constructor to pass a derived visitor
	protected ExprCnfChecker(ExprCNFVisitor visitor) {
		this.visitor = visitor;
	}
	
	public boolean isExprCNF(Expr<? extends BoolType> expr) {
		return expr.accept(visitor, CNFStatus.START);
	}

	protected enum CNFStatus {
		START(0), INSIDE_AND(1), INSIDE_OR(2), INSIDE_NOT(3);
		private final int value;
	    private CNFStatus(int value) { this.value = value; }
	    public int getValue() { return value; }
	}

	protected static class ExprCNFVisitor implements ExprVisitor<CNFStatus, Boolean> {

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
		public <ExprType extends Type> Boolean visit(IteExpr<ExprType> expr, CNFStatus param) {
			return false;
		}
		
	}
}
