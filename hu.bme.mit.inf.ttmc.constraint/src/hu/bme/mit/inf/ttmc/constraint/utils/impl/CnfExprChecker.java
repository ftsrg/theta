package hu.bme.mit.inf.ttmc.constraint.utils.impl;

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
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

/**
 * CNF checker to decide if an expression is in conjunctive
 * normal form (CNF).
 * 
 * Also serves as a base class for checking CNF for extensions
 * of the constraint language. The implementation contains a
 * helper visitor, which must be extended by the classes
 * inheriting from this class.
 * 
 * @author Akos
 *
 */
public class CnfExprChecker {
	
	private IsCnfExprVisitor visitor;
	
	/**
	 * Constructor.
	 */
	public CnfExprChecker() {
		visitor = getCnfExprVisitor();
	}
	
	/**
	 * Check if the expression is in conjunctive normal form (CNF).
	 * @param expr Expression to be checked
	 * @return True if the expression is in CNF, false otherwise
	 */
	public boolean isExprInCnf(Expr<? extends BoolType> expr) {
		return expr.accept(visitor, Status.START);
	}
	
	/**
	 * Get the helper visitor.
	 * @return Helper visitor
	 */
	protected IsCnfExprVisitor getCnfExprVisitor() {
		return new IsCnfExprVisitor();
	}

	/**
	 * Enum for keeping track of the current state in the visitor.
	 * @author Akos
	 */
	protected enum Status {
		START(0), AND(1), OR(2), NOT(3);
		private final int value;
	    private Status(int value) { this.value = value; }
	    public int getValue() { return value; }
	}

	/**
	 * Helper visitor for checking if an expression is in CNF.
	 * @author Akos
	 */
	protected class IsCnfExprVisitor implements ExprVisitor<Status, Boolean> {

		@Override
		public <DeclType extends Type> Boolean visit(ConstRefExpr<DeclType> expr, Status param) {
			return true;
		}

		@Override
		public <DeclType extends Type> Boolean visit(ParamRefExpr<DeclType> expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(FalseExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(TrueExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(NotExpr expr, Status param) {
			// NOT is not allowed inside NOT
			if(param.getValue() >= Status.NOT.getValue()) return false;
			else return expr.getOp().accept(this, Status.NOT);
		}

		@Override
		public Boolean visit(ImplyExpr expr, Status param) {
			return false;
		}

		@Override
		public Boolean visit(IffExpr expr, Status param) {
			return false;
		}

		@Override
		public Boolean visit(AndExpr expr, Status param) {
			// AND is allowed inside AND
			if(param.getValue() > Status.AND.getValue()) return false;
			else return expr.getOps().stream().allMatch(op -> op.accept(this, Status.AND));
		}

		@Override
		public Boolean visit(OrExpr expr, Status param) {
			// OR is allowed inside OR
			if(param.getValue() > Status.OR.getValue()) return false;
			else return expr.getOps().stream().allMatch(op -> op.accept(this, Status.OR));
		}

		@Override
		public Boolean visit(ExistsExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(ForallExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(EqExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(NeqExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(GeqExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(GtExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(LeqExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(LtExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(IntLitExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(IntDivExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(RemExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(ModExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(RatLitExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(RatDivExpr expr, Status param) {
			return true;
		}

		@Override
		public <ExprType extends ClosedUnderNeg> Boolean visit(NegExpr<ExprType> expr, Status param) {
			return true;
		}

		@Override
		public <ExprType extends ClosedUnderSub> Boolean visit(SubExpr<ExprType> expr, Status param) {
			return true;
		}

		@Override
		public <ExprType extends ClosedUnderAdd> Boolean visit(AddExpr<ExprType> expr, Status param) {
			return true;
		}

		@Override
		public <ExprType extends ClosedUnderMul> Boolean visit(MulExpr<ExprType> expr, Status param) {
			return true;
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Boolean visit(ArrayReadExpr<IndexType, ElemType> expr,
				Status param) {
			return true;
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Boolean visit(ArrayWriteExpr<IndexType, ElemType> expr,
				Status param) {
			return true;
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Boolean visit(FuncLitExpr<ParamType, ResultType> expr,
				Status param) {
			return true;
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Boolean visit(FuncAppExpr<ParamType, ResultType> expr,
				Status param) {
			return true;
		}

		@Override
		public Boolean visit(TupleLitExpr expr, Status param) {
			return true;
		}

		@Override
		public Boolean visit(TupleProjExpr expr, Status param) {
			return true;
		}

		@Override
		public <ExprType extends Type> Boolean visit(IteExpr<ExprType> expr, Status param) {
			return false;
		}
		
	}
}
