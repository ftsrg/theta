package hu.bme.mit.theta.frontend.c.dependency;

import java.util.Set;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.AndExpr;
import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.FalseExpr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.IntDivExpr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.ModExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.MultiaryExpr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.expr.NotExpr;
import hu.bme.mit.theta.core.expr.OrExpr;
import hu.bme.mit.theta.core.expr.ProcCallExpr;
import hu.bme.mit.theta.core.expr.RatDivExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.expr.TrueExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.core.utils.impl.FailExprVisitor;

public class VariableFinderVisitor extends FailExprVisitor<Set<VarDecl<? extends Type>>, Set<VarDecl<? extends Type>>> {

	private Set<VarDecl<? extends Type>> processBinary(
			final BinaryExpr<? extends Type, ? extends Type, ? extends Type> expr,
			final Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return param;
	}

	private Set<VarDecl<? extends Type>> processMultiary(final MultiaryExpr<? extends Type, ? extends Type> expr,
			final Set<VarDecl<? extends Type>> param) {
		expr.getOps().forEach(o -> o.accept(this, param));
		return param;
	}

	private Set<VarDecl<? extends Type>> processUnary(final UnaryExpr<? extends Type, ? extends Type> expr,
			final Set<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);
		return param;
	}

	/// Var references

	@Override
	public <DeclType extends Type> Set<VarDecl<? extends Type>> visit(final VarRefExpr<DeclType> expr,
			final Set<VarDecl<? extends Type>> param) {
		param.add(expr.getDecl());
		return param;
	}

	/// Multiary operators

	@Override
	public <ExprType extends ClosedUnderAdd> Set<VarDecl<? extends Type>> visit(final AddExpr<ExprType> expr,
			final Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final AndExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Set<VarDecl<? extends Type>> visit(final MulExpr<ExprType> expr,
			final Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final OrExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	/// Binary operators

	@Override
	public <ExprType extends ClosedUnderSub> Set<VarDecl<? extends Type>> visit(final SubExpr<ExprType> expr,
			final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final EqExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final NeqExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final GeqExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final LeqExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final GtExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final LtExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final ModExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final IntDivExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final RatDivExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	/// Unary operators

	@Override
	public Set<VarDecl<? extends Type>> visit(final NotExpr expr, final Set<VarDecl<? extends Type>> param) {
		return this.processUnary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Set<VarDecl<? extends Type>> visit(final NegExpr<ExprType> expr,
			final Set<VarDecl<? extends Type>> param) {
		return this.processUnary(expr, param);
	}

	/// Literals

	@Override
	public Set<VarDecl<? extends Type>> visit(final IntLitExpr expr, final Set<VarDecl<? extends Type>> param) {
		return param;
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final FalseExpr expr, final Set<VarDecl<? extends Type>> param) {
		return param;
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(final TrueExpr expr, final Set<VarDecl<? extends Type>> param) {
		return param;
	}

	@Override
	public <ReturnType extends Type> Set<VarDecl<? extends Type>> visit(final ProcCallExpr<ReturnType> expr,
			final Set<VarDecl<? extends Type>> param) {
		expr.getParams().forEach(arg -> arg.accept(this, param));

		return param;
	}

}
