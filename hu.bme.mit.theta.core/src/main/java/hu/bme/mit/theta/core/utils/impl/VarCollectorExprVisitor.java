package hu.bme.mit.theta.core.utils.impl;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.FuncAppExpr;
import hu.bme.mit.theta.core.expr.FuncLitExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.QuantifiedExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;

final class VarCollectorExprVisitor extends ArityBasedExprVisitor<Collection<VarDecl<? extends Type>>, Void> {

	private static final VarCollectorExprVisitor INSTANCE;

	static {
		INSTANCE = new VarCollectorExprVisitor();
	}

	private VarCollectorExprVisitor() {
	}

	public static VarCollectorExprVisitor getInstance() {
		return INSTANCE;
	}

	@Override
	public <DeclType extends Type> Void visit(final RefExpr<DeclType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		final Decl<DeclType> decl = expr.getDecl();
		if (decl instanceof VarDecl) {
			final VarDecl<DeclType> var = (VarDecl<DeclType>) decl;
			param.add(var);
		}
		return null;
	}

	@Override
	protected <ExprType extends Type> Void visitNullary(final NullaryExpr<ExprType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		return null;
	}

	@Override
	protected <OpType extends Type, ExprType extends Type> Void visitUnary(final UnaryExpr<OpType, ExprType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);
		return null;
	}

	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Void visitBinary(
			final BinaryExpr<LeftOpType, RightOpType, ExprType> expr, final Collection<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);
		return null;
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Void visitMultiary(
			final MultiaryExpr<OpsType, ExprType> expr, final Collection<VarDecl<? extends Type>> param) {
		for (final Expr<? extends OpsType> op : expr.getOps())
			op.accept(this, param);
		return null;
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Void visitQuantified(final QuantifiedExpr expr,
			final Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(final ArrayReadExpr<IndexType, ElemType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		expr.getArray().accept(this, param);
		expr.getIndex().accept(this, param);
		return null;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(final ArrayWriteExpr<IndexType, ElemType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(final FuncLitExpr<ParamType, ResultType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(final FuncAppExpr<ParamType, ResultType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ReturnType extends Type> Void visit(final ProcCallExpr<ReturnType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ExprType extends Type> Void visit(final IteExpr<ExprType> expr,
			final Collection<VarDecl<? extends Type>> param) {
		expr.getCond().accept(this, param);
		expr.getThen().accept(this, param);
		expr.getElse().accept(this, param);
		return null;
	}

}
