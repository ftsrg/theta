package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableSet;

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
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ExprITERemoverVisitor extends ArityBasedExprVisitor<Void, Expr<? extends Type>> {
	
	private ConstraintManager manager;
	
	public ExprITERemoverVisitor(ConstraintManager manager) {
		this.manager = manager;
	}

	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(NullaryExpr<ExprType> expr, Void param) {
		return expr;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(
			UnaryExpr<OpType, ExprType> expr, Void param) {
		return expr.withOp((Expr<? extends OpType>) expr.getOp().accept(this, param));
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, Void param) {
		return expr.withOps(
				(Expr<? extends LeftOpType>)expr.getLeftOp().accept(this, param),
				(Expr<? extends RightOpType>)expr.getRightOp().accept(this, param));
	}

	@SuppressWarnings("unchecked")
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

	@SuppressWarnings("unchecked")
	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(IteExpr<ExprType> expr, Void param) {
		ExprFactory fact = manager.getExprFactory();
		// Apply ite(C,T,E) <=> (!C or T) and (C or E) transformation
		Expr<? extends BoolType> cond = (Expr<? extends BoolType>)expr.getCond().accept(this, param);
		Expr<? extends Type> then = expr.getThen().accept(this, param);
		Expr<? extends Type> elze = expr.getElse().accept(this, param);
		return fact.And(ImmutableSet.of(
				fact.Or(ImmutableSet.of(fact.Not(cond), (Expr<? extends BoolType>)then)),
				fact.Or(ImmutableSet.of(cond, (Expr<? extends BoolType>)elze))
				));
	}

}
