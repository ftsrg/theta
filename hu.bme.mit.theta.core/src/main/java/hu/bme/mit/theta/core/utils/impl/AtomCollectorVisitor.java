package hu.bme.mit.theta.core.utils.impl;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.ModExpr;
import hu.bme.mit.theta.core.type.inttype.RemExpr;
import hu.bme.mit.theta.core.type.proctype.ProcCallExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public class AtomCollectorVisitor implements ExprVisitor<Collection<Expr<? extends BoolType>>, Void> {

	protected Void visitNonBoolConnective(final Expr<? extends Type> expr,
			final Collection<Expr<? extends BoolType>> param) {
		param.add(TypeUtils.cast(expr, BoolType.class));
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(final RefExpr<DeclType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends Type> Void visit(final PrimedExpr<ExprType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final FalseExpr expr, final Collection<Expr<? extends BoolType>> param) {
		param.add(expr);
		return null;
	}

	@Override
	public Void visit(final TrueExpr expr, final Collection<Expr<? extends BoolType>> param) {
		param.add(expr);
		return null;
	}

	@Override
	public Void visit(final NotExpr expr, final Collection<Expr<? extends BoolType>> param) {
		expr.getOp().accept(this, param);
		return null;
	}

	@Override
	public Void visit(final ImplyExpr expr, final Collection<Expr<? extends BoolType>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);
		return null;
	}

	@Override
	public Void visit(final IffExpr expr, final Collection<Expr<? extends BoolType>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);
		return null;
	}

	@Override
	public Void visit(final AndExpr expr, final Collection<Expr<? extends BoolType>> param) {
		expr.getOps().forEach(op -> op.accept(this, param));
		return null;
	}

	@Override
	public Void visit(final OrExpr expr, final Collection<Expr<? extends BoolType>> param) {
		expr.getOps().forEach(op -> op.accept(this, param));
		return null;
	}

	@Override
	public Void visit(final ExistsExpr expr, final Collection<Expr<? extends BoolType>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public Void visit(final ForallExpr expr, final Collection<Expr<? extends BoolType>> param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public Void visit(final EqExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final NeqExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final GeqExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final GtExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final LeqExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final LtExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final IntLitExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final IntDivExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final RemExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final ModExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final RatLitExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public Void visit(final RatDivExpr expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Void visit(final NegExpr<ExprType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderSub> Void visit(final SubExpr<ExprType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Void visit(final AddExpr<ExprType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Void visit(final MulExpr<ExprType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(final ArrayReadExpr<IndexType, ElemType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Void visit(final ArrayWriteExpr<IndexType, ElemType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(final FuncLitExpr<ParamType, ResultType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Void visit(final FuncAppExpr<ParamType, ResultType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ReturnType extends Type> Void visit(final ProcCallExpr<ReturnType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends Type> Void visit(final IteExpr<ExprType> expr,
			final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

}
