package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.Collection;

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
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class VarCollectorVisitor extends ArityBasedExprVisitor<Collection<VarDecl<? extends Type>>, Void>
		implements ExprVisitor<Collection<VarDecl<? extends Type>>, Void>,
		FormalismExprVisitor<Collection<VarDecl<? extends Type>>, Void> {

	@Override
	public <ExprType extends Type> Void visit(PrimedExpr<ExprType> expr, Collection<VarDecl<? extends Type>> param) {
		return visitUnary(expr, param);
	}

	@Override
	public <ReturnType extends Type> Void visit(ProcCallExpr<ReturnType> expr,
			Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ReturnType extends Type> Void visit(ProcRefExpr<ReturnType> expr,
			Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <DeclType extends Type> Void visit(VarRefExpr<DeclType> expr, Collection<VarDecl<? extends Type>> param) {
		param.add(expr.getDecl());
		return null;
	}

	@Override
	protected <ExprType extends Type> Void visitNullary(NullaryExpr<ExprType> expr,
			Collection<VarDecl<? extends Type>> param) {
		return null;
	}

	@Override
	protected <OpType extends Type, ExprType extends Type> Void visitUnary(UnaryExpr<OpType, ExprType> expr,
			Collection<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);
		return null;
	}

	@Override
	protected <LeftOpType extends Type, RightOpType extends Type, ExprType extends Type> Void visitBinary(
			BinaryExpr<LeftOpType, RightOpType, ExprType> expr, Collection<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);
		return null;
	}

	@Override
	protected <OpsType extends Type, ExprType extends Type> Void visitMultiary(MultiaryExpr<OpsType, ExprType> expr,
			Collection<VarDecl<? extends Type>> param) {
		for (Expr<? extends OpsType> op : expr.getOps()) op.accept(this, param);
		return null;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(ArrayReadExpr<IndexType, ElemType> expr,
			Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(ArrayWriteExpr<IndexType, ElemType> expr,
			Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(FuncLitExpr<ParamType, ResultType> expr,
			Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(FuncAppExpr<ParamType, ResultType> expr,
			Collection<VarDecl<? extends Type>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ExprType extends Type> Void visit(IteExpr<ExprType> expr, Collection<VarDecl<? extends Type>> param) {
		expr.getCond().accept(this, param);
		expr.getThen().accept(this, param);
		expr.getElse().accept(this, param);
		return null;
	}

}
