package hu.bme.mit.inf.theta.frontend.transform;

import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Add;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Bool;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Geq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Gt;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.IntDiv;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Leq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Lt;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Mod;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Mul;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Neq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Or;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Neg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import hu.bme.mit.inf.theta.core.expr.AddExpr;
import hu.bme.mit.inf.theta.core.expr.AndExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.theta.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.theta.core.expr.BoolLitExpr;
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
import hu.bme.mit.inf.theta.core.expr.LitExpr;
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
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.impl.Exprs2;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.ProcCallExprVisitor;
import hu.bme.mit.inf.theta.formalism.common.expr.visitor.VarRefExprVisitor;

public class ConstantFolderExprVisitor implements VarRefExprVisitor<Void, Expr<? extends Type>>, ProcCallExprVisitor<Void, Expr<? extends Type>> {

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
		Expr<? extends Type> res = expr.getOp().accept(this, param);

		if (res instanceof BoolLitExpr) {
			BoolLitExpr lit = (BoolLitExpr) res;

			return Bool(!lit.getValue());
		}

		return Not(ExprUtils.cast(res, BoolType.class));
	}

	@Override
	public Expr<? extends Type> visit(AndExpr expr, Void param) {
		List<Expr<? extends BoolType>> newOps = new ArrayList<>();

		boolean ans = true;
		for (Expr<? extends Type> operand : expr.getOps()) {
			Expr<? extends Type> res = operand.accept(this, param);
			if (res instanceof BoolLitExpr) {
				BoolLitExpr lit = (BoolLitExpr) res;
				if (lit.getValue() == false) {
					return False();
				}

				ans = ans && lit.getValue();
			}

			newOps.add(ExprUtils.cast(res, BoolType.class));
		}

		// if it was all constants
		if (newOps.size() == 0)
			return Bool(ans);

		// if the product did not change
		if (expr.getOps().size() == newOps.size())
			return And(newOps);

		newOps.add(Bool(ans));
		return And(newOps);
	}

	@Override
	public Expr<? extends Type> visit(OrExpr expr, Void param) {
		List<Expr<? extends BoolType>> newOps = new ArrayList<>();

		boolean ans = false;
		for (Expr<? extends Type> operand : expr.getOps()) {
			Expr<? extends Type> res = operand.accept(this, param);
			if (res instanceof BoolLitExpr) {
				BoolLitExpr lit = (BoolLitExpr) res;
				if (lit.getValue() == true) {
					return True();
				}

				ans = ans || lit.getValue();
			}

			newOps.add(ExprUtils.cast(res, BoolType.class));
		}

		// if it was all constants
		if (newOps.size() == 0)
			return Bool(ans);

		// if the product did not change
		if (expr.getOps().size() == newOps.size())
			return Or(newOps);

		newOps.add(Bool(ans));
		return Or(newOps);
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
		Expr<? extends Type> res = expr.getOp().accept(this, param);

		if (res instanceof IntLitExpr) {
			return Int(-1 * ((IntLitExpr) res).getValue());
		}

		return Neg(ExprUtils.cast(res, ClosedUnderNeg.class));
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
		List<Expr<? extends ClosedUnderAdd>> newOps = new ArrayList<>();

		int sum = 0;
		for (Expr<? extends ExprType> operand : expr.getOps()) {
			Expr<? extends Type> res = operand.accept(this, param);
			if (res instanceof IntLitExpr) {
				IntLitExpr lit = (IntLitExpr) res;
				sum += lit.getValue();
			} else {
				newOps.add(ExprUtils.cast(res, ClosedUnderAdd.class));
			}
		}

		// if it was all constants
		if (newOps.size() == 0)
			return Int(sum);

		// if the product did not change
		if (sum == 0)
			return Add(newOps);

		newOps.add(Int(sum));
		return Add(newOps);
	}

	@Override
	public <ExprType extends ClosedUnderMul> Expr<? extends Type> visit(MulExpr<ExprType> expr, Void param) {
		List<Expr<? extends ClosedUnderMul>> newOps = new ArrayList<>();

		int product = 1;
		for (Expr<? extends ExprType> operand : expr.getOps()) {
			Expr<? extends Type> res = operand.accept(this, param);
			if (res instanceof IntLitExpr) {
				IntLitExpr lit = (IntLitExpr) res;
				if (lit.getValue() == 0)
					return Int(0);

				product *= lit.getValue();
			} else {
				newOps.add(ExprUtils.cast(res, ClosedUnderMul.class));
			}
		}

		// if it was all constants
		if (newOps.size() == 0)
			return Int(product);

		// if the product did not change
		if (product == 1)
			return Mul(newOps);

		newOps.add(Int(product));
		return Mul(newOps);
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

	@Override
	public <ReturnType extends Type> Expr<? extends Type> visit(ProcCallExpr<ReturnType> expr, Void param) {
		List<Expr<? extends Type>> newArgs = new ArrayList<>();
		for (Expr<? extends Type> arg : expr.getParams()) {
			newArgs.add(arg.accept(this, param));
		}

		return Exprs2.Call(expr.getProc(), newArgs);
	}

}
