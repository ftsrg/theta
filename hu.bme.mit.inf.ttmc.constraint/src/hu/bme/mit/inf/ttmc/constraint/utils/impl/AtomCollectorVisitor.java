package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import java.util.Collection;

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
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

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
