package hu.bme.mit.inf.theta.frontend.transform.expr;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.core.decl.impl.Decls;
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
import hu.bme.mit.inf.theta.core.expr.impl.Exprs;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;
import hu.bme.mit.inf.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.VarRefExprVisitor;
import hu.bme.mit.inf.theta.frontend.ir.node.AssertNode;
import hu.bme.mit.inf.theta.frontend.ir.node.AssignNode;
import hu.bme.mit.inf.theta.frontend.ir.node.BranchTableNode;
import hu.bme.mit.inf.theta.frontend.ir.node.GotoNode;
import hu.bme.mit.inf.theta.frontend.ir.node.IrNode;
import hu.bme.mit.inf.theta.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.theta.frontend.ir.node.NodeFactory;
import hu.bme.mit.inf.theta.frontend.ir.node.ReturnNode;

public class VariableRefactorExprVisitor implements ExprVisitor<Void, Expr<? extends Type>>, VarRefExprVisitor<Void, Expr<? extends Type>> {

	private final String suffix;
	private final Map<VarDecl<? extends Type>, VarDecl<? extends Type>> varMap = new HashMap<>();
	private final Map<VarDecl<? extends Type>, Expr<? extends Type>> boundParams;

	public VariableRefactorExprVisitor(String suffix, Map<VarDecl<? extends Type>, Expr<? extends Type>> boundParams) {
		this.suffix = suffix;
		this.boundParams = boundParams;
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(ConstRefExpr<DeclType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(ParamRefExpr<DeclType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(FalseExpr expr, Void param) {
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(TrueExpr expr, Void param) {
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(NotExpr expr, Void param) {
		Expr<? extends BoolType> op = ExprUtils.cast(expr.getOp().accept(this, param), BoolType.class);

		return expr.withOp(op);
	}

	@Override
	public Expr<? extends Type> visit(ImplyExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(IffExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(AndExpr expr, Void param) {
		List<Expr<? extends BoolType>> ops = expr.getOps()
			.stream()
			.map(e -> {
				Expr<? extends BoolType> result = ExprUtils.cast(e.accept(this, param), BoolType.class);
				return result;
			})
			.collect(Collectors.toList());

		return expr.withOps(ops);
	}

	@Override
	public Expr<? extends Type> visit(OrExpr expr, Void param) {
		List<Expr<? extends BoolType>> ops = expr.getOps()
				.stream()
				.map(e -> {
					Expr<? extends BoolType> result = ExprUtils.cast(e.accept(this, param), BoolType.class);
					return result;
				})
				.collect(Collectors.toList());

		return expr.withOps(ops);
	}

	@Override
	public Expr<? extends Type> visit(ExistsExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(ForallExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(EqExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(NeqExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(GeqExpr expr, Void param) {
		Expr<? extends RatType> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		Expr<? extends RatType> right = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(GtExpr expr, Void param) {
		Expr<? extends RatType> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		Expr<? extends RatType> right = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(LeqExpr expr, Void param) {
		Expr<? extends RatType> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		Expr<? extends RatType> right = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(LtExpr expr, Void param) {
		Expr<? extends RatType> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		Expr<? extends RatType> right = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(IntLitExpr expr, Void param) {
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(IntDivExpr expr, Void param) {
		Expr<? extends IntType> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), IntType.class);
		Expr<? extends IntType> right = ExprUtils.cast(expr.getRightOp().accept(this, param), IntType.class);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(RemExpr expr, Void param) {
		Expr<? extends IntType> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), IntType.class);
		Expr<? extends IntType> right = ExprUtils.cast(expr.getRightOp().accept(this, param), IntType.class);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(ModExpr expr, Void param) {
		Expr<? extends IntType> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), IntType.class);
		Expr<? extends IntType> right = ExprUtils.cast(expr.getRightOp().accept(this, param), IntType.class);

		return expr.withOps(left, right);
	}

	@Override
	public Expr<? extends Type> visit(RatLitExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(RatDivExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Expr<? extends Type> visit(NegExpr<ExprType> expr, Void param) {
		Expr<? extends ClosedUnderNeg> op = ExprUtils.cast(expr.getOp().accept(this, param), ClosedUnderNeg.class);

		return Exprs.Neg(op);
	}

	@Override
	public <ExprType extends ClosedUnderSub> Expr<? extends Type> visit(SubExpr<ExprType> expr, Void param) {
		Expr<? extends ClosedUnderSub> left = ExprUtils.cast(expr.getLeftOp().accept(this, param), ClosedUnderSub.class);
		Expr<? extends ClosedUnderSub> right = ExprUtils.cast(expr.getRightOp().accept(this, param), ClosedUnderSub.class);

		return Exprs.Sub(left, right);
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Expr<? extends Type> visit(AddExpr<ExprType> expr, Void param) {
		List<Expr<? extends ClosedUnderAdd>> ops = expr.getOps()
				.stream()
				.map(e -> {
					Expr<? extends ClosedUnderAdd> result = ExprUtils.cast(e.accept(this, param), ClosedUnderAdd.class);
					return result;
				})
				.collect(Collectors.toList());

		return Exprs.Add(ops);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Expr<? extends Type> visit(MulExpr<ExprType> expr, Void param) {
		List<Expr<? extends ClosedUnderMul>> ops = expr.getOps()
				.stream()
				.map(e -> {
					Expr<? extends ClosedUnderMul> result = ExprUtils.cast(e.accept(this, param), ClosedUnderMul.class);
					return result;
				})
				.collect(Collectors.toList());

		return Exprs.Mul(ops);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayReadExpr<IndexType, ElemType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayWriteExpr<IndexType, ElemType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncLitExpr<ParamType, ResultType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncAppExpr<ParamType, ResultType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(IteExpr<ExprType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(VarRefExpr<DeclType> expr, Void param) {
		// Is this a bound param?
		VarDecl<? extends Type> var = expr.getDecl();
		if (this.boundParams.containsKey(var)) {
			return this.boundParams.get(var);
		}

		if (this.varMap.containsKey(var)) {
			return this.varMap.get(var).getRef();
		} else {
			// We encountered a new variable, need to rename it
			VarDecl<? extends Type> newVar = Decls2.Var(var.getName() + "_" + suffix, var.getType());
			this.varMap.put(var, newVar);

			return newVar.getRef();
		}
	}

	public void refactor(IrNode node) {
		if (node instanceof AssignNode<?, ?>) {
			@SuppressWarnings("unchecked")
			AssignNode<? extends Type, ? extends Type> assign = (AssignNode<? extends Type, ? extends Type>) node;
			Expr<? extends Type> expr = assign.getExpr().accept(this, null);

			assign.setExpr(expr);
		} else if (node instanceof AssertNode) {
			AssertNode check = (AssertNode) node;
			Expr<? extends Type> res = check.getCond().accept(this, null);

			check.setCond(ExprUtils.cast(res, BoolType.class));
		} else if (node instanceof JumpIfNode) {
			JumpIfNode branch = (JumpIfNode) node;
			Expr<? extends Type> res = branch.getCondition().accept(this, null);

			branch.setCondition(ExprUtils.cast(res, BoolType.class));
		} else if (node instanceof BranchTableNode) {
			BranchTableNode bt = (BranchTableNode) node;
			Expr<? extends Type> res = bt.getCondition().accept(this, null);

			bt.setCondition(res);
		} else if (node instanceof ReturnNode) {
			ReturnNode ret = (ReturnNode) node;
			ret.setExpr(ret.getExpr().accept(this, null));
		}
	}
}
