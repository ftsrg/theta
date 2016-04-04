package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.AddExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.ExistsExpr;
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
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.constraint.z3.decl.Z3Decl;

class Z3ExprVisitor implements ExprVisitor<Void, com.microsoft.z3.Expr> {

	private final Z3Transformator transformator;
	private final Context context;

	private final com.microsoft.z3.BoolExpr falseTerm;
	private final com.microsoft.z3.BoolExpr trueTerm;

	Z3ExprVisitor(final Z3Transformator transformator, final Context context) {
		this.context = context;
		this.transformator = transformator;

		falseTerm = context.mkFalse();
		trueTerm = context.mkTrue();
	}

	////

	@Override
	public <DeclType extends Type> com.microsoft.z3.Expr visit(final ConstRefExpr<DeclType> expr, final Void param) {
		final com.microsoft.z3.FuncDecl funcDecl = transformator.transform(expr.getDecl());
		return context.mkConst(funcDecl);
	}

	@Override
	public <DeclType extends Type> com.microsoft.z3.Expr visit(final ParamRefExpr<DeclType> expr, final Void param) {
		final com.microsoft.z3.FuncDecl funcDecl = transformator.transform(expr.getDecl());
		return context.mkConst(funcDecl);
	}

	@Override
	public com.microsoft.z3.Expr visit(final FalseExpr expr, final Void param) {
		return falseTerm;
	}

	@Override
	public com.microsoft.z3.Expr visit(final TrueExpr expr, final Void param) {
		return trueTerm;
	}

	@Override
	public com.microsoft.z3.Expr visit(final NotExpr expr, final Void param) {
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) expr.getOp().accept(this, param);
		return context.mkNot(opTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final ImplyExpr expr, final Void param) {
		final com.microsoft.z3.BoolExpr leftOpTerm = (com.microsoft.z3.BoolExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.BoolExpr rightOpTerm = (com.microsoft.z3.BoolExpr) expr.getRightOp().accept(this, param);
		return context.mkImplies(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final IffExpr expr, final Void param) {
		final com.microsoft.z3.BoolExpr leftOpTerm = (com.microsoft.z3.BoolExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.BoolExpr rightOpTerm = (com.microsoft.z3.BoolExpr) expr.getRightOp().accept(this, param);
		return context.mkIff(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final AndExpr expr, final Void param) {
		final com.microsoft.z3.BoolExpr[] opTerms = expr.getOps().stream().map(e -> e.accept(this, param))
				.toArray(size -> new com.microsoft.z3.BoolExpr[size]);
		return context.mkAnd(opTerms);
	}

	@Override
	public com.microsoft.z3.Expr visit(final OrExpr expr, final Void param) {
		final com.microsoft.z3.BoolExpr[] opTerms = expr.getOps().stream().map(e -> e.accept(this, param))
				.toArray(size -> new com.microsoft.z3.BoolExpr[size]);
		return context.mkOr(opTerms);
	}

	@Override
	public com.microsoft.z3.Expr visit(final ExistsExpr expr, final Void param) {
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) expr.getOp().accept(this, param);
		final com.microsoft.z3.Expr[] paramTerms = new com.microsoft.z3.Expr[expr.getParamDecls().size()];

		int i = 0;
		for (final ParamDecl<?> paramDecl : expr.getParamDecls()) {
			final Z3Decl<?, ?> z3ParamDecl = (Z3Decl<?, ?>) paramDecl;
			final com.microsoft.z3.FuncDecl paramSymbol = z3ParamDecl.getSymbol();
			paramTerms[i] = context.mkConst(paramSymbol);
			i++;
		}

		return context.mkExists(paramTerms, opTerm, 1, null, null, null, null);
	}

	@Override
	public com.microsoft.z3.Expr visit(final ForallExpr expr, final Void param) {
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) expr.getOp().accept(this, param);
		final com.microsoft.z3.Expr[] paramTerms = new com.microsoft.z3.Expr[expr.getParamDecls().size()];

		int i = 0;
		for (final ParamDecl<?> paramDecl : expr.getParamDecls()) {
			final Z3Decl<?, ?> z3ParamDecl = (Z3Decl<?, ?>) paramDecl;
			final com.microsoft.z3.FuncDecl paramSymbol = z3ParamDecl.getSymbol();
			paramTerms[i] = context.mkConst(paramSymbol);
			i++;
		}

		return context.mkForall(paramTerms, opTerm, 1, null, null, null, null);
	}

	@Override
	public com.microsoft.z3.Expr visit(final EqExpr expr, final Void param) {
		final com.microsoft.z3.Expr leftOpTerm = expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.Expr rightOpTerm = expr.getRightOp().accept(this, param);
		return context.mkEq(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final NeqExpr expr, final Void param) {
		final com.microsoft.z3.Expr leftOpTerm = expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.Expr rightOpTerm = expr.getRightOp().accept(this, param);
		return context.mkDistinct(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final GeqExpr expr, final Void param) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) expr.getRightOp().accept(this,
				param);
		return context.mkGe(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final GtExpr expr, final Void param) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) expr.getRightOp().accept(this,
				param);
		return context.mkGt(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final LeqExpr expr, final Void param) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) expr.getRightOp().accept(this,
				param);
		return context.mkLe(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final LtExpr expr, final Void param) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) expr.getRightOp().accept(this,
				param);
		return context.mkLt(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final IntLitExpr expr, final Void param) {
		return context.mkInt(expr.getValue());
	}

	@Override
	public com.microsoft.z3.Expr visit(final IntDivExpr expr, final Void param) {
		final com.microsoft.z3.IntExpr leftOpTerm = (com.microsoft.z3.IntExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.IntExpr rightOpTerm = (com.microsoft.z3.IntExpr) expr.getRightOp().accept(this, param);
		return context.mkDiv(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final RemExpr expr, final Void param) {
		final com.microsoft.z3.IntExpr leftOpTerm = (com.microsoft.z3.IntExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.IntExpr rightOpTerm = (com.microsoft.z3.IntExpr) expr.getRightOp().accept(this, param);
		return context.mkRem(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final ModExpr expr, final Void param) {
		final com.microsoft.z3.IntExpr leftOpTerm = (com.microsoft.z3.IntExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.IntExpr rightOpTerm = (com.microsoft.z3.IntExpr) expr.getRightOp().accept(this, param);
		return context.mkMod(leftOpTerm, rightOpTerm);
	}

	@Override
	public com.microsoft.z3.Expr visit(final RatLitExpr expr, final Void param) {
		return context.mkReal(Math.toIntExact(expr.getNum()), Math.toIntExact(expr.getDenom()));
	}

	@Override
	public com.microsoft.z3.Expr visit(final RatDivExpr expr, final Void param) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) expr.getRightOp().accept(this,
				param);
		return context.mkDiv(leftOpTerm, rightOpTerm);
	}

	@Override
	public <ExprType extends ClosedUnderNeg> com.microsoft.z3.Expr visit(final NegExpr<ExprType> expr,
			final Void param) {
		final com.microsoft.z3.ArithExpr opTerm = (com.microsoft.z3.ArithExpr) expr.getOp().accept(this, param);
		return context.mkUnaryMinus(opTerm);
	}

	@Override
	public <ExprType extends ClosedUnderSub> com.microsoft.z3.Expr visit(final SubExpr<ExprType> expr,
			final Void param) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) expr.getLeftOp().accept(this, param);
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) expr.getRightOp().accept(this,
				param);
		return context.mkSub(leftOpTerm, rightOpTerm);
	}

	@Override
	public <ExprType extends ClosedUnderAdd> com.microsoft.z3.Expr visit(final AddExpr<ExprType> expr,
			final Void param) {
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(e -> e.accept(this, param))
				.toArray(size -> new com.microsoft.z3.ArithExpr[size]);
		return context.mkAdd(opTerms);
	}

	@Override
	public <ExprType extends ClosedUnderMul> com.microsoft.z3.Expr visit(final MulExpr<ExprType> expr,
			final Void param) {
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(e -> e.accept(this, param))
				.toArray(size -> new com.microsoft.z3.ArithExpr[size]);
		return context.mkMul(opTerms);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> com.microsoft.z3.Expr visit(
			final ArrayReadExpr<IndexType, ElemType> expr, final Void param) {
		final com.microsoft.z3.ArrayExpr arrayTerm = (com.microsoft.z3.ArrayExpr) expr.getArray().accept(this, param);
		final com.microsoft.z3.Expr indexTerm = expr.getIndex().accept(this, param);
		return context.mkSelect(arrayTerm, indexTerm);
	}

	@Override
	public <IndexType extends Type, ElemType extends Type> com.microsoft.z3.Expr visit(
			final ArrayWriteExpr<IndexType, ElemType> expr, final Void param) {
		final com.microsoft.z3.ArrayExpr arrayTerm = (com.microsoft.z3.ArrayExpr) expr.getArray().accept(this, param);
		final com.microsoft.z3.Expr indexTerm = expr.getIndex().accept(this, param);
		final com.microsoft.z3.Expr elemExpr = expr.getElem().accept(this, param);
		return context.mkStore(arrayTerm, indexTerm, elemExpr);
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> com.microsoft.z3.Expr visit(
			final FuncLitExpr<ParamType, ResultType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ParamType extends Type, ResultType extends Type> com.microsoft.z3.Expr visit(
			final FuncAppExpr<ParamType, ResultType> expr, final Void param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <ExprType extends Type> com.microsoft.z3.Expr visit(final IteExpr<ExprType> expr, final Void param) {
		final com.microsoft.z3.BoolExpr condTerm = (com.microsoft.z3.BoolExpr) expr.getCond().accept(this, param);
		final com.microsoft.z3.Expr thenTerm = expr.getThen().accept(this, param);
		final com.microsoft.z3.Expr elzeTerm = expr.getElse().accept(this, param);
		return context.mkITE(condTerm, thenTerm, elzeTerm);
	}

}
