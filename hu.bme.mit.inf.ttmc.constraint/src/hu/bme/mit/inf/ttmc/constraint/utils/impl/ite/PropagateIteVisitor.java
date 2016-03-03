package hu.bme.mit.inf.ttmc.constraint.utils.impl.ite;

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
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.constraint.utils.impl.ArityBasedExprVisitor;

/**
 * Propagate ITE up in the expression tree as high as possible
 * @author Akos
 *
 */
public class PropagateIteVisitor extends ArityBasedExprVisitor<Void, Expr<? extends Type>> {
	private ExprVisitor<Void, Expr<? extends Type>> pushBelowIteVisitor;
	
	/**
	 * Constructor.
	 * @param manager Constraint manager
	 * @param pushBelowIteVisitor Visitor which can push below an ITE
	 */
	public PropagateIteVisitor(ConstraintManager manager, ExprVisitor<Void, Expr<? extends Type>> pushBelowIteVisitor) {
		this.pushBelowIteVisitor = pushBelowIteVisitor;
	}
	
	@Override
	protected <ExprType extends Type> Expr<? extends Type> visitNullary(NullaryExpr<ExprType> expr, Void param) {
		return expr;
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpType extends Type, ExprType extends Type> Expr<? extends Type> visitUnary(
			UnaryExpr<OpType, ExprType> expr, Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		return expr.withOp((Expr<? extends OpType>) expr.getOp().accept(this, param)).accept(pushBelowIteVisitor, param);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		return expr.withOps(
				(Expr<? extends LeftOpType>) expr.getLeftOp().accept(this, param),
				(Expr<? extends RightOpType>) expr.getRightOp().accept(this, param))
				.accept(pushBelowIteVisitor, param);
	}

	@SuppressWarnings("unchecked")
	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, Void param) {
		// Apply propagation to operand(s) first, then apply pushdown
		List<Expr<? extends OpsType>> ops = new ArrayList<>(expr.getOps().size());
		for (Expr<? extends OpsType> op : expr.getOps()) ops.add((Expr<? extends OpsType>) op.accept(this, param));
		return expr.withOps(ops).accept(pushBelowIteVisitor, param);
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
		// Apply propagation to operand(s)
		return expr.withOps(
				expr.getCond(),
				(Expr<? extends ExprType>) expr.getThen().accept(this, param),
				(Expr<? extends ExprType>) expr.getElse().accept(this, param));
	}

}
