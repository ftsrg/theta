package hu.bme.mit.inf.theta.core.utils.impl;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.AddExpr;
import hu.bme.mit.inf.theta.core.expr.AndExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.theta.core.expr.ConstRefExpr;
import hu.bme.mit.inf.theta.core.expr.EqExpr;
import hu.bme.mit.inf.theta.core.expr.ExistsExpr;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.FalseExpr;
import hu.bme.mit.inf.theta.core.expr.ForallExpr;
import hu.bme.mit.inf.theta.core.expr.FuncAppExpr;
import hu.bme.mit.inf.theta.core.expr.FuncLitExpr;
import hu.bme.mit.inf.theta.core.expr.GeqExpr;
import hu.bme.mit.inf.theta.core.expr.GtExpr;
import hu.bme.mit.inf.theta.core.expr.IffExpr;
import hu.bme.mit.inf.theta.core.expr.ImplyExpr;
import hu.bme.mit.inf.theta.core.expr.IntDivExpr;
import hu.bme.mit.inf.theta.core.expr.IntLitExpr;
import hu.bme.mit.inf.theta.core.expr.IteExpr;
import hu.bme.mit.inf.theta.core.expr.LeqExpr;
import hu.bme.mit.inf.theta.core.expr.LtExpr;
import hu.bme.mit.inf.theta.core.expr.ModExpr;
import hu.bme.mit.inf.theta.core.expr.MulExpr;
import hu.bme.mit.inf.theta.core.expr.NegExpr;
import hu.bme.mit.inf.theta.core.expr.NeqExpr;
import hu.bme.mit.inf.theta.core.expr.NotExpr;
import hu.bme.mit.inf.theta.core.expr.OrExpr;
import hu.bme.mit.inf.theta.core.expr.ParamRefExpr;
import hu.bme.mit.inf.theta.core.expr.RatDivExpr;
import hu.bme.mit.inf.theta.core.expr.RatLitExpr;
import hu.bme.mit.inf.theta.core.expr.RemExpr;
import hu.bme.mit.inf.theta.core.expr.SubExpr;
import hu.bme.mit.inf.theta.core.expr.TrueExpr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;

public class AtomCollectorVisitor implements ExprVisitor<Collection<Expr<? extends BoolType>>, Void> {

	protected Void visitNonBoolConnective(final Expr<? extends Type> expr, final Collection<Expr<? extends BoolType>> param) {
		param.add(ExprUtils.cast(expr, BoolType.class));
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(final ConstRefExpr<DeclType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <DeclType extends Type> Void visit(final ParamRefExpr<DeclType> expr, final Collection<Expr<? extends BoolType>> param) {
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
		for (final Expr<? extends BoolType> op : expr.getOps())
			op.accept(this, param);
		return null;
	}

	@Override
	public Void visit(final OrExpr expr, final Collection<Expr<? extends BoolType>> param) {
		for (final Expr<? extends BoolType> op : expr.getOps())
			op.accept(this, param);
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
	public <ExprType extends ClosedUnderNeg> Void visit(final NegExpr<ExprType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderSub> Void visit(final SubExpr<ExprType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Void visit(final AddExpr<ExprType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Void visit(final MulExpr<ExprType> expr, final Collection<Expr<? extends BoolType>> param) {
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
	public <ExprType extends Type> Void visit(final IteExpr<ExprType> expr, final Collection<Expr<? extends BoolType>> param) {
		return visitNonBoolConnective(expr, param);
	}

}
