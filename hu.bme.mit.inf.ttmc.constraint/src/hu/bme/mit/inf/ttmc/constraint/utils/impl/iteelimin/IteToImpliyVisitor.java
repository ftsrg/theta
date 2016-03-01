package hu.bme.mit.inf.ttmc.constraint.utils.impl.iteelimin;

import java.util.ArrayList;
import java.util.List;

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
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ArityBasedVisitor;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class IteToImpliyVisitor extends ArityBasedVisitor<Void, Expr<? extends Type>> {
	
	private ConstraintManager manager;
	
	public IteToImpliyVisitor(ConstraintManager manager) {
		this.manager = manager;
	}

	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(NullaryExpr<ExprType> expr, Void param) {
		return expr;
	}

	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(
			UnaryExpr<OpType, ExprType> expr, Void param) {
		Expr<? extends Type> op = expr.getOp().accept(this, param);
		return expr.withOp((Expr<? extends OpType>)op);
	}

	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, Void param) {
		Expr<? extends Type> leftOp = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> rightOp = expr.getRightOp().accept(this, param);
		return expr.withOps((Expr<? extends LeftOpType>)leftOp, (Expr<? extends RightOpType>)rightOp);
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, Void param) {
		List<Expr<? extends OpsType>> ops = new ArrayList<>(expr.getOps().size());
		for (Expr<? extends OpsType> op : expr.getOps())
			ops.add((Expr<? extends OpsType>) op.accept(this, param));
		return expr.withOps(ops);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayReadExpr<IndexType, ElemType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayWriteExpr<IndexType, ElemType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncLitExpr<ParamType, ResultType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncAppExpr<ParamType, ResultType> expr, Void param) {
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(IteExpr<ExprType> expr, Void param) {
		ExprFactory fact = manager.getExprFactory();
		Expr<? extends BoolType> cond = (Expr<? extends BoolType>)expr.getCond().accept(this, param);
		Expr<? extends Type> then = expr.getThen().accept(this, param);
		Expr<? extends Type> elze = expr.getElse().accept(this, param);
		return fact.And(
				fact.Or(fact.Not(cond), (Expr<? extends BoolType>)then),
				fact.Or(cond, (Expr<? extends BoolType>)elze)
				);
	}

}
