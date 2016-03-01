package hu.bme.mit.inf.ttmc.constraint.utils.impl.iteelimin;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.IteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.MultiaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ArityBasedVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.IsBooleanConnectiveVisitor;

public class PushBelowIteVisitor extends ArityBasedVisitor<Void, Expr<? extends Type>> {
	
	private ConstraintManager manager;
	private IsBooleanConnectiveVisitor isBooleanVisitor;
	
	public PushBelowIteVisitor(ConstraintManager manager) {
		this.manager = manager;
		isBooleanVisitor = new IsBooleanConnectiveVisitor();
	}

	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(NullaryExpr<ExprType> expr, Void param) {
		return expr;
	}

	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(
			UnaryExpr<OpType, ExprType> expr, Void param) {
		// Nothing to do if the operand is not an ITE or it is of bool type
		if (!(expr.getOp() instanceof IteExpr) || expr.accept(isBooleanVisitor, null)) {
			return expr;
		} else {
			IteExpr<? extends OpType> op = (IteExpr<? extends OpType>) expr.getOp();
			return manager.getExprFactory().Ite(op.getCond(), expr.withOp(op.getThen()).accept(this, param), expr.withOp(op.getElse()).accept(this, param));
		}
		
	}
	
	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayReadExpr<IndexType, ElemType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayWriteExpr<IndexType, ElemType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncLitExpr<ParamType, ResultType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncAppExpr<ParamType, ResultType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(IteExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return null;
	}

}
