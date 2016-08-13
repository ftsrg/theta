package hu.bme.mit.inf.ttmc.frontend.transform;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Bool;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Gt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.IntDiv;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Mod;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Mul;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Sub;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.core.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IffExpr;
import hu.bme.mit.inf.ttmc.core.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.IteExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.ModExpr;
import hu.bme.mit.inf.ttmc.core.expr.MulExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.VarRefExprVisitor;

public class ConstantFolderExprVisitor implements VarRefExprVisitor<Void, Expr<? extends Type>> {

	private Map<VarDecl<? extends Type>, LitExpr<? extends Type>> constVars;

	public Map<VarDecl<? extends Type>, LitExpr<? extends Type>> getConstVars() {
		return constVars;
	}

	public ConstantFolderExprVisitor(Map<VarDecl<? extends Type>, LitExpr<? extends Type>> constVars) {
		this.constVars = constVars;
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(VarRefExpr<DeclType> expr, Void param) {
		if (this.constVars.containsKey(expr.getDecl())) {
			// This variable has a constant value, thus can be replaced by a constant.
			return this.constVars.get(expr.getDecl());
		}

		return expr;
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
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(AndExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(OrExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(EqExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Bool(leftLit.getValue() == rightLit.getValue());
		}

		return Eq(left, right);
	}

	@Override
	public Expr<? extends Type> visit(NeqExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Bool(leftLit.getValue() != rightLit.getValue());
		}

		return Neq(left, right);
	}

	@Override
	public Expr<? extends Type> visit(GeqExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Bool(leftLit.getValue() >= rightLit.getValue());
		}

		return Geq(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
	}

	@Override
	public Expr<? extends Type> visit(GtExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Bool(leftLit.getValue() > rightLit.getValue());
		}

		return Gt(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
	}

	@Override
	public Expr<? extends Type> visit(LeqExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Bool(leftLit.getValue() <= rightLit.getValue());
		}

		return Leq(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
	}

	@Override
	public Expr<? extends Type> visit(LtExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Bool(leftLit.getValue() < rightLit.getValue());
		}

		return Lt(ExprUtils.cast(left, RatType.class), ExprUtils.cast(right, RatType.class));
	}

	@Override
	public Expr<? extends Type> visit(IntLitExpr expr, Void param) {
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(IntDivExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		// The operands are constants - we can calculate their value compile time
		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Int(leftLit.getValue() / rightLit.getValue());
		}

		return IntDiv(ExprUtils.cast(left, IntType.class), ExprUtils.cast(right, IntType.class));
	}

	@Override
	public Expr<? extends Type> visit(RemExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(ModExpr expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		// The operands are constants - we can calculate their value compile time
		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Int(leftLit.getValue() % rightLit.getValue());
		}

		return Mod(ExprUtils.cast(left, IntType.class), ExprUtils.cast(right, IntType.class));
	}

	@Override
	public Expr<? extends Type> visit(RatLitExpr expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(RatDivExpr expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Expr<? extends Type> visit(NegExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
	}

	@Override
	public <ExprType extends ClosedUnderSub> Expr<? extends Type> visit(SubExpr<ExprType> expr, Void param) {
		Expr<? extends Type> left = expr.getLeftOp().accept(this, param);
		Expr<? extends Type> right = expr.getRightOp().accept(this, param);

		// The operands are constants, we can calculate their value compile time
		if (left instanceof IntLitExpr && right instanceof IntLitExpr) {
			IntLitExpr leftLit = (IntLitExpr) left;
			IntLitExpr rightLit = (IntLitExpr) right;

			return Int(leftLit.getValue() - rightLit.getValue());
		}

		return Sub(ExprUtils.cast(left, ClosedUnderSub.class), ExprUtils.cast(right, ClosedUnderSub.class));
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Expr<? extends Type> visit(AddExpr<ExprType> expr, Void param) {
		int constCount = 0;
		List<Expr<? extends ClosedUnderAdd>> allOps = new ArrayList<>();

		/* Find all constant operations */
		for (Expr<? extends Type> s : expr.getOps()) {
			Expr<? extends Type> res = s.accept(this, param);
			if (res instanceof LitExpr<?>) {
				constCount++;
			}
			allOps.add(ExprUtils.cast(res, ClosedUnderAdd.class));
		}

		/* If all operands are constants, we can calculate their value compile time */
		if (constCount == allOps.size()) {
			long sum = 0;
			for (Expr<? extends Type> s : allOps) {
				sum += ((IntLitExpr) s).getValue();
			}

			return Int(sum);
		}

		return Add(allOps);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Expr<? extends Type> visit(MulExpr<ExprType> expr, Void param) {
		int constCount = 0;
		List<Expr<? extends ClosedUnderMul>> allOps = new ArrayList<>();

		/* Find all constant operations */
		for (Expr<? extends Type> s : expr.getOps()) {
			Expr<? extends Type> res = s.accept(this, param);
			if (res instanceof LitExpr<?>) {
				constCount++;
			}
			allOps.add(ExprUtils.cast(res, ClosedUnderMul.class));
		}

		/* If all operands are constants, we can calculate their value compile time */
		if (constCount == allOps.size()) {
			long sum = 1;
			for (Expr<? extends Type> s : allOps) {
				sum *= ((IntLitExpr) s).getValue();
			}

			return Int(sum);
		}

		return Mul(allOps);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayReadExpr<IndexType, ElemType> expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(
			ArrayWriteExpr<IndexType, ElemType> expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncLitExpr<ParamType, ResultType> expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(
			FuncAppExpr<ParamType, ResultType> expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
	}

	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(IteExpr<ExprType> expr, Void param) {
		// TODO Auto-generated method stub
		return expr;
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
	public <DeclType extends Type> Expr<? extends Type> visit(ConstRefExpr<DeclType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(ParamRefExpr<DeclType> expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(ImplyExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Expr<? extends Type> visit(IffExpr expr, Void param) {
		throw new UnsupportedOperationException();
	}

}
