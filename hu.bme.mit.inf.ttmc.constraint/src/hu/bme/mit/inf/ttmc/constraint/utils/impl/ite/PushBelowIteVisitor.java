package hu.bme.mit.inf.ttmc.constraint.utils.impl.ite;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

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

/**
 * Push an expression below an ITE recursively
 * @author Akos
 *
 */
class PushBelowIteVisitor extends ArityBasedVisitor<Void, Expr<? extends Type>> {
	
	private ConstraintManager manager;
	private IsBooleanConnectiveVisitor isBooleanVisitor;
	
	/**
	 * Constructor.
	 * @param manager Constraint manager
	 */
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
			// Push expression below ITE, e.g., -ite(C,T,E) => ite(C,-T,-E)
			IteExpr<? extends OpType> op = (IteExpr<? extends OpType>) expr.getOp();
			return manager.getExprFactory().Ite(op.getCond(), expr.withOp(op.getThen()).accept(this, param), expr.withOp(op.getElse()).accept(this, param));
		}
		
	}
	
	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Expr<? extends Type> visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, Void param) {
		// Nothing to do if the none of the operands are ITE or it is of bool type
		if (!(expr.getLeftOp() instanceof IteExpr || expr.getRightOp() instanceof IteExpr) || expr.accept(isBooleanVisitor, null)) {
			return expr;
		} else if (expr.getLeftOp() instanceof IteExpr) {
			// Push expression below ITE, e.g., ite(C,T,E) = X => ite(C,T=X,E=X)
			IteExpr<? extends LeftOpType> op = (IteExpr<? extends LeftOpType>) expr.getLeftOp();
			return manager.getExprFactory().Ite(
					op.getCond(),
					expr.withLeftOp(op.getThen()).accept(this, param),
					expr.withLeftOp(op.getElse()).accept(this, param));
		} else /* expr.getRightOp() must be an ITE */ {
			// Push expression below ITE, e.g., X = ite(C,T,E) => ite(C,x=T,X=E)
			IteExpr<? extends RightOpType> op = (IteExpr<? extends RightOpType>) expr.getRightOp();
			return manager.getExprFactory().Ite(
					op.getCond(),
					expr.withRightOp(op.getThen()).accept(this, param),
					expr.withRightOp(op.getElse()).accept(this, param));
		}
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Expr<? extends Type> visitMultiary(
			MultiaryExpr<OpsType, ExprType> expr, Void param) {
		// Get the first operand which is an ITE
		Optional<? extends Expr<? extends OpsType>> firstIte = expr.getOps().stream().filter(op -> op instanceof IteExpr).findFirst();
		// Nothing to do if the none of the operands are ITE or it is of bool type
		if (!firstIte.isPresent() || expr.accept(isBooleanVisitor, null)) {
			return expr;
		} else {
			// Push expression below ITE, e.g., X + ite(C,T,E) + Y  => ite(C,X+T+Y,X+E+Y)
			List<Expr<? extends OpsType>> thenOps = new ArrayList<>(expr.getOps().size());
			List<Expr<? extends OpsType>> elseOps = new ArrayList<>(expr.getOps().size());
			IteExpr<? extends OpsType> ite = (IteExpr<? extends OpsType>) firstIte.get();

			for (Expr<? extends OpsType> op : expr.getOps()) {
				if (op == ite) {
					thenOps.add(ite.getThen());
					elseOps.add(ite.getElse());
				} else {
					thenOps.add(op);
					elseOps.add(op);
				}
			}
			
			return manager.getExprFactory().Ite(
					ite.getCond(),
					expr.withOps(thenOps).accept(this, param),
					expr.withOps(elseOps).accept(this, param));
		}
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
		return expr;
	}

}
