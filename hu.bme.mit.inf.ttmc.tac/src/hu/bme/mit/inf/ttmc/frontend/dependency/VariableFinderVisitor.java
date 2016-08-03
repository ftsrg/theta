package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.Set;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.ModExpr;
import hu.bme.mit.inf.ttmc.core.expr.MulExpr;
import hu.bme.mit.inf.ttmc.core.expr.MultiaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.impl.FailExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.VarRefExprVisitor;

public class VariableFinderVisitor
	extends FailExprVisitor<Set<VarDecl<? extends Type>>, Set<VarDecl<? extends Type>>>
	implements VarRefExprVisitor<Set<VarDecl<? extends Type>>, Set<VarDecl<? extends Type>>>
{


	private Set<VarDecl<? extends Type>> processBinary(BinaryExpr<? extends Type, ? extends Type, ? extends Type> expr, Set<VarDecl<? extends Type>> param) {
		expr.getLeftOp().accept(this, param);
		expr.getRightOp().accept(this, param);

		return param;
	}

	private Set<VarDecl<? extends Type>> processMultiary(MultiaryExpr<? extends Type, ? extends Type> expr, Set<VarDecl<? extends Type>> param) {
		expr.getOps().forEach(o -> o.accept(this, param));
		return param;
	}

	private Set<VarDecl<? extends Type>> processUnary(UnaryExpr<? extends Type, ? extends Type> expr, Set<VarDecl<? extends Type>> param) {
		expr.getOp().accept(this, param);
		return param;
	}

	/// Var references

	@Override
	public <DeclType extends Type> Set<VarDecl<? extends Type>> visit(VarRefExpr<DeclType> expr, Set<VarDecl<? extends Type>> param) {
		param.add(expr.getDecl());
		return param;
	}

	/// Multiary operators

	@Override
	public <ExprType extends ClosedUnderAdd> Set<VarDecl<? extends Type>> visit(AddExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(AndExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Set<VarDecl<? extends Type>> visit(MulExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(OrExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processMultiary(expr, param);
	}

	/// Binary operators

	@Override
	public <ExprType extends ClosedUnderSub> Set<VarDecl<? extends Type>> visit(SubExpr<ExprType> expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(EqExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(NeqExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(GeqExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(LeqExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(GtExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(LtExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(ModExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(IntDivExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(RatDivExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processBinary(expr, param);
	}

	/// Unary operators

	@Override
	public Set<VarDecl<? extends Type>> visit(NotExpr expr, Set<VarDecl<? extends Type>> param) {
		return this.processUnary(expr, param);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Set<VarDecl<? extends Type>> visit(NegExpr<ExprType> expr,
			Set<VarDecl<? extends Type>> param) {
		return this.processUnary(expr, param);
	}

	/// Literals

	@Override
	public Set<VarDecl<? extends Type>> visit(IntLitExpr expr, Set<VarDecl<? extends Type>> param) {
		return param;
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(FalseExpr expr, Set<VarDecl<? extends Type>> param) {
		return param;
	}

	@Override
	public Set<VarDecl<? extends Type>> visit(TrueExpr expr, Set<VarDecl<? extends Type>> param) {
		return param;
	}

}
