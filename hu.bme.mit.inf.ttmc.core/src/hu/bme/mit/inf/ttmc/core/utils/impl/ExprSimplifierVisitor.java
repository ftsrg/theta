package hu.bme.mit.inf.ttmc.core.utils.impl;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

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
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.model.Model;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;

public class ExprSimplifierVisitor implements ExprVisitor<Model, Expr<? extends Type>> {

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(final ConstRefExpr<DeclType> expr, final Model param) {
		final Optional<Expr<DeclType>> eval = param.eval(expr.getDecl());
		if (eval.isPresent()) {
			return eval.get();
		}

		return expr;
	}

	@Override
	public <DeclType extends Type> Expr<? extends Type> visit(final ParamRefExpr<DeclType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public Expr<? extends Type> visit(final FalseExpr expr, final Model param) {
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(final TrueExpr expr, final Model param) {
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(final NotExpr expr, final Model param) {
		final Expr<? extends BoolType> op = ExprUtils.cast(expr.getOp().accept(this, param), BoolType.class);
		if (op instanceof NotExpr)
			return ((NotExpr) op).getOp();
		else if (op instanceof TrueExpr)
			return Exprs.False();
		else if (op instanceof FalseExpr)
			return Exprs.True();

		return Exprs.Not(op);
	}

	@Override
	public Expr<? extends Type> visit(final ImplyExpr expr, final Model param) {
		return Exprs.Or(Exprs.Not(expr.getLeftOp()), expr.getRightOp()).accept(this, param);
	}

	@Override
	public Expr<? extends Type> visit(final IffExpr expr, final Model param) {
		if (expr.getLeftOp().equals(expr.getRightOp())) {
			return Exprs.True();
		}
		return Exprs.And(Exprs.Not(expr.getLeftOp()), expr.getRightOp(), expr.getLeftOp(), Exprs.Not(expr.getRightOp())).accept(this, param);
	}

	@Override
	public Expr<? extends Type> visit(final AndExpr expr, final Model param) {
		final Set<Expr<? extends BoolType>> ops = new HashSet<>();
		for (final Expr<? extends BoolType> op : expr.getOps()) {
			final Expr<? extends BoolType> opMapped = ExprUtils.cast(op.accept(this, param), BoolType.class);
			if (opMapped instanceof TrueExpr) {
				continue;
			} else if (opMapped instanceof FalseExpr) {
				return Exprs.False();
			} else if (opMapped instanceof AndExpr) {
				ops.addAll(((AndExpr) opMapped).getOps());
			} else {
				ops.add(opMapped);
			}
		}

		if (ops.size() == 0) {
			return Exprs.True();
		} else if (ops.size() == 1) {
			return ops.iterator().next();
		}
		return Exprs.And(ops);
	}

	@Override
	public Expr<? extends Type> visit(final OrExpr expr, final Model param) {
		final Set<Expr<? extends BoolType>> ops = new HashSet<>();
		for (final Expr<? extends BoolType> op : expr.getOps()) {
			final Expr<? extends BoolType> opMapped = ExprUtils.cast(op.accept(this, param), BoolType.class);
			if (opMapped instanceof FalseExpr) {
				continue;
			} else if (opMapped instanceof TrueExpr) {
				return Exprs.True();
			} else if (opMapped instanceof OrExpr) {
				ops.addAll(((OrExpr) opMapped).getOps());
			} else {
				ops.add(opMapped);
			}
		}

		if (ops.size() == 0) {
			return Exprs.True();
		} else if (ops.size() == 1) {
			return ops.iterator().next();
		}
		return Exprs.Or(ops);
	}

	@Override
	public Expr<? extends Type> visit(final ExistsExpr expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public Expr<? extends Type> visit(final ForallExpr expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public Expr<? extends Type> visit(final EqExpr expr, final Model param) {
		final Expr<? extends Type> leftOp = expr.getLeftOp().accept(this, param);
		final Expr<? extends Type> rightOp = expr.getRightOp().accept(this, param);
		if (leftOp.equals(rightOp))
			return Exprs.True();

		return Exprs.Eq(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final NeqExpr expr, final Model param) {
		final Expr<? extends Type> leftOp = expr.getLeftOp().accept(this, param);
		final Expr<? extends Type> rightOp = expr.getRightOp().accept(this, param);
		if (leftOp.equals(rightOp))
			return Exprs.False();

		return Exprs.Neq(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final GeqExpr expr, final Model param) {
		final Expr<? extends RatType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		final Expr<? extends RatType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		if (leftOp.equals(rightOp))
			return Exprs.True();

		if ((leftOp instanceof RatLitExpr || leftOp instanceof IntLitExpr) && (rightOp instanceof RatLitExpr || rightOp instanceof IntLitExpr)) {
			long leftNum = 0, leftDenom = 1, rightNum = 0, rightDenom = 1;
			if (leftOp instanceof IntLitExpr) {
				leftNum = ((IntLitExpr) leftOp).getValue();
			} else {
				leftNum = ((RatLitExpr) leftOp).getNum();
				leftDenom = ((RatLitExpr) leftOp).getDenom();
			}
			if (rightOp instanceof IntLitExpr) {
				rightNum = ((IntLitExpr) rightOp).getValue();
			} else {
				rightNum = ((RatLitExpr) rightOp).getNum();
				rightDenom = ((RatLitExpr) rightOp).getDenom();
			}

			assert (leftDenom > 0);
			assert (rightDenom > 0);

			return Exprs.Bool(leftNum * rightDenom >= rightNum * leftDenom);
		}

		return Exprs.Geq(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final GtExpr expr, final Model param) {
		final Expr<? extends RatType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		final Expr<? extends RatType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		// TODO

		return Exprs.Gt(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final LeqExpr expr, final Model param) {
		final Expr<? extends RatType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		final Expr<? extends RatType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		// TODO

		return Exprs.Leq(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final LtExpr expr, final Model param) {
		final Expr<? extends RatType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		final Expr<? extends RatType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		// TODO

		return Exprs.Geq(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final IntLitExpr expr, final Model param) {
		return expr;
	}

	@Override
	public Expr<? extends Type> visit(final IntDivExpr expr, final Model param) {
		final Expr<? extends IntType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), IntType.class);
		final Expr<? extends IntType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), IntType.class);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final long leftInt = ((IntLitExpr) leftOp).getValue();
			final long rightInt = ((IntLitExpr) rightOp).getValue();
			assert (rightInt != 0);
			return Exprs.Int(leftInt / rightInt);
		}

		if (leftOp.equals(Exprs.Int(0)))
			return Exprs.Int(0);

		if (leftOp.equals(rightOp))
			return Exprs.Int(1);

		return Exprs.IntDiv(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final RemExpr expr, final Model param) {
		final Expr<? extends IntType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), IntType.class);
		final Expr<? extends IntType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), IntType.class);

		// TODO

		return Exprs.Rem(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final ModExpr expr, final Model param) {
		final Expr<? extends IntType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), IntType.class);
		final Expr<? extends IntType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), IntType.class);

		if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
			final IntLitExpr leftLit = (IntLitExpr) leftOp;
			final IntLitExpr rightLit = (IntLitExpr) rightOp;
			return Exprs.Int(leftLit.getValue() % rightLit.getValue());
		}

		if (leftOp.equals(rightOp))
			return Exprs.Int(0);

		return Exprs.IntDiv(leftOp, rightOp);
	}

	@Override
	public Expr<? extends Type> visit(final RatLitExpr expr, final Model param) {

		long denom = expr.getDenom();
		long num = expr.getNum();

		if (denom < 0) {
			denom *= -1;
			num *= -1;
		} else if (denom == 0) {
			throw new ArithmeticException("Division by zero");
		}

		if (num == 0) {
			return Exprs.Int(0);
		} else if (num % denom == 0) {
			return Exprs.Int(num / denom);
		}

		return Exprs.Rat(num, denom);
	}

	@Override
	public Expr<? extends Type> visit(final RatDivExpr expr, final Model param) {
		final Expr<? extends RatType> leftOp = ExprUtils.cast(expr.getLeftOp().accept(this, param), RatType.class);
		final Expr<? extends RatType> rightOp = ExprUtils.cast(expr.getRightOp().accept(this, param), RatType.class);

		// TODO

		return Exprs.RatDiv(leftOp, rightOp);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> Expr<? extends Type> visit(final NegExpr<ExprType> expr, final Model param) {
		final Expr<? extends ClosedUnderNeg> op = ExprUtils.cast(expr.getOp().accept(this, param), ClosedUnderNeg.class);

		if (op instanceof IntLitExpr) {
			return Exprs.Int(((IntLitExpr) op).getValue() * -1);
		} else if (op instanceof RatLitExpr) {
			final RatLitExpr opLit = ((RatLitExpr) op);
			return Exprs.Rat(opLit.getNum() * -1, opLit.getDenom());
		} else if (op instanceof NegExpr) {
			return ((NegExpr<? extends ClosedUnderNeg>) op).getOp();
		}

		return Exprs.Neg(op);
	}

	@Override
	public <ExprType extends ClosedUnderSub> Expr<? extends Type> visit(final SubExpr<ExprType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ExprType extends ClosedUnderAdd> Expr<? extends Type> visit(final AddExpr<ExprType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ExprType extends ClosedUnderMul> Expr<? extends Type> visit(final MulExpr<ExprType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(final ArrayReadExpr<IndexType, ElemType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> Expr<? extends Type> visit(final ArrayWriteExpr<IndexType, ElemType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(final FuncLitExpr<ParamType, ResultType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> Expr<? extends Type> visit(final FuncAppExpr<ParamType, ResultType> expr, final Model param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO");
	}

	@Override
	public <ExprType extends Type> Expr<? extends Type> visit(final IteExpr<ExprType> expr, final Model param) {
		final Expr<? extends BoolType> cond = ExprUtils.cast(expr.getCond().accept(this, param), BoolType.class);
		final Expr<? extends Type> then = expr.getThen().accept(this, param);
		final Expr<? extends Type> elze = expr.getElse().accept(this, param);

		if (cond.equals(Exprs.True())) {
			return then;
		} else if (cond.equals(Exprs.False())) {
			return elze;
		}

		return Exprs.Ite(cond, then, elze);
	}

}
