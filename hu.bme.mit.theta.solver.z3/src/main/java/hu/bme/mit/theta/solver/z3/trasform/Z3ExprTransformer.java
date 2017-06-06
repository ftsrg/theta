package hu.bme.mit.theta.solver.z3.trasform;

import java.util.concurrent.ExecutionException;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import com.microsoft.z3.Context;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.ModExpr;
import hu.bme.mit.theta.core.type.inttype.RemExpr;
import hu.bme.mit.theta.core.type.rattype.RatAddExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatEqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGtExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;
import hu.bme.mit.theta.core.type.rattype.RatMulExpr;
import hu.bme.mit.theta.core.type.rattype.RatNegExpr;
import hu.bme.mit.theta.core.type.rattype.RatNeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;

class Z3ExprTransformer {

	private static final int CACHE_SIZE = 1000;

	private final Z3TransformationManager transformer;
	private final Context context;

	private final Cache<Expr<?>, com.microsoft.z3.Expr> exprToTerm;
	private final DispatchTable<com.microsoft.z3.Expr> table;

	Z3ExprTransformer(final Z3TransformationManager transformer, final Context context) {
		this.context = context;
		this.transformer = transformer;

		exprToTerm = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

		table = DispatchTable.<com.microsoft.z3.Expr>builder()

				// General

				.addCase(RefExpr.class, this::transformRef)

				.addCase(IteExpr.class, this::transformIte)

				// Boolean

				.addCase(FalseExpr.class, this::transformFalse)

				.addCase(TrueExpr.class, this::transformTrue)

				.addCase(NotExpr.class, this::transformNot)

				.addCase(ImplyExpr.class, this::transformImply)

				.addCase(IffExpr.class, this::transformIff)

				.addCase(AndExpr.class, this::transformAnd)

				.addCase(OrExpr.class, this::transformOr)

				.addCase(ExistsExpr.class, this::transformExists)

				.addCase(ForallExpr.class, this::transformForall)

				// Rationals

				.addCase(RatLitExpr.class, this::transformRatLit)

				.addCase(RatAddExpr.class, this::transformRatAdd)

				.addCase(RatSubExpr.class, this::transformRatSub)

				.addCase(RatNegExpr.class, this::transformRatNeg)

				.addCase(RatMulExpr.class, this::transformRatMul)

				.addCase(RatDivExpr.class, this::transformRatDiv)

				.addCase(RatEqExpr.class, this::transformRatEq)

				.addCase(RatNeqExpr.class, this::transformRatNeq)

				.addCase(RatGeqExpr.class, this::transformRatGeq)

				.addCase(RatGtExpr.class, this::transformRatGt)

				.addCase(RatLeqExpr.class, this::transformRatLeq)

				.addCase(RatLtExpr.class, this::transformRatLt)

				// Integers

				.addCase(IntLitExpr.class, this::transformIntLit)

				.addCase(IntAddExpr.class, this::transformIntAdd)

				.addCase(IntSubExpr.class, this::transformIntSub)

				.addCase(IntNegExpr.class, this::transformIntNeg)

				.addCase(IntMulExpr.class, this::transformIntMul)

				.addCase(IntDivExpr.class, this::transformIntDiv)

				.addCase(ModExpr.class, this::transformMod)

				.addCase(RemExpr.class, this::transformRem)

				.addCase(IntEqExpr.class, this::transformIntEq)

				.addCase(IntNeqExpr.class, this::transformIntNeq)

				.addCase(IntGeqExpr.class, this::transformIntGeq)

				.addCase(IntGtExpr.class, this::transformIntGt)

				.addCase(IntLeqExpr.class, this::transformIntLeq)

				.addCase(IntLtExpr.class, this::transformIntLt)

				.build();
	}

	public com.microsoft.z3.Expr toTerm(final Expr<?> expr) {
		try {
			return exprToTerm.get(expr, () -> table.dispatch(expr));
		} catch (final ExecutionException e) {
			throw new AssertionError();
		}
	}

	////

	/*
	 * General
	 */

	private com.microsoft.z3.Expr transformRef(final RefExpr<?> expr) {
		final Decl<?> decl = expr.getDecl();
		final com.microsoft.z3.FuncDecl funcDecl = transformer.toSymbol(decl);
		return context.mkConst(funcDecl);
	}

	private com.microsoft.z3.Expr transformIte(final IteExpr<?> expr) {
		final com.microsoft.z3.BoolExpr condTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getCond());
		final com.microsoft.z3.Expr thenTerm = toTerm(expr.getThen());
		final com.microsoft.z3.Expr elzeTerm = toTerm(expr.getElse());
		return context.mkITE(condTerm, thenTerm, elzeTerm);
	}

	/*
	 * Booleans
	 */

	private com.microsoft.z3.Expr transformFalse(final FalseExpr expr) {
		return context.mkFalse();

	}

	private com.microsoft.z3.Expr transformTrue(final TrueExpr expr) {
		return context.mkTrue();
	}

	private com.microsoft.z3.Expr transformNot(final NotExpr expr) {
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getOp());
		return context.mkNot(opTerm);
	}

	private com.microsoft.z3.Expr transformImply(final ImplyExpr expr) {
		final com.microsoft.z3.BoolExpr leftOpTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.BoolExpr rightOpTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getRightOp());
		return context.mkImplies(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformIff(final IffExpr expr) {
		final com.microsoft.z3.BoolExpr leftOpTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.BoolExpr rightOpTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getRightOp());
		return context.mkIff(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformAnd(final AndExpr expr) {
		final com.microsoft.z3.BoolExpr[] opTerms = expr.getOps().stream().map(e -> toTerm(e))
				.toArray(size -> new com.microsoft.z3.BoolExpr[size]);
		return context.mkAnd(opTerms);
	}

	private com.microsoft.z3.Expr transformOr(final OrExpr expr) {
		final com.microsoft.z3.BoolExpr[] opTerms = expr.getOps().stream().map(e -> toTerm(e))
				.toArray(size -> new com.microsoft.z3.BoolExpr[size]);
		return context.mkOr(opTerms);
	}

	private com.microsoft.z3.Expr transformExists(final ExistsExpr expr) {
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getOp());
		final com.microsoft.z3.Expr[] paramTerms = new com.microsoft.z3.Expr[expr.getParamDecls().size()];

		int i = 0;
		for (final ParamDecl<?> paramDecl : expr.getParamDecls()) {
			final com.microsoft.z3.FuncDecl paramSymbol = transformer.toSymbol(paramDecl);
			paramTerms[i] = context.mkConst(paramSymbol);
			i++;
		}

		return context.mkExists(paramTerms, opTerm, 1, null, null, null, null);
	}

	private com.microsoft.z3.Expr transformForall(final ForallExpr expr) {
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getOp());
		final com.microsoft.z3.Expr[] paramTerms = new com.microsoft.z3.Expr[expr.getParamDecls().size()];

		int i = 0;
		for (final ParamDecl<?> paramDecl : expr.getParamDecls()) {
			final com.microsoft.z3.FuncDecl paramSymbol = transformer.toSymbol(paramDecl);
			paramTerms[i] = context.mkConst(paramSymbol);
			i++;
		}

		return context.mkForall(paramTerms, opTerm, 1, null, null, null, null);
	}

	/*
	 * Rationals
	 */

	private com.microsoft.z3.Expr transformRatLit(final RatLitExpr expr) {
		return context.mkReal(Math.toIntExact(expr.getNum()), Math.toIntExact(expr.getDenom()));
	}

	private com.microsoft.z3.Expr transformRatAdd(final RatAddExpr expr) {
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(e -> toTerm(e))
				.toArray(size -> new com.microsoft.z3.ArithExpr[size]);
		return context.mkAdd(opTerms);
	}

	private com.microsoft.z3.Expr transformRatSub(final RatSubExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkSub(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformRatNeg(final RatNegExpr expr) {
		final com.microsoft.z3.ArithExpr opTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getOp());
		return context.mkUnaryMinus(opTerm);
	}

	private com.microsoft.z3.Expr transformRatMul(final RatMulExpr expr) {
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(e -> toTerm(e))
				.toArray(size -> new com.microsoft.z3.ArithExpr[size]);
		return context.mkMul(opTerms);
	}

	private com.microsoft.z3.Expr transformRatDiv(final RatDivExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkDiv(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformRatEq(final RatEqExpr expr) {
		final com.microsoft.z3.Expr leftOpTerm = toTerm(expr.getLeftOp());
		final com.microsoft.z3.Expr rightOpTerm = toTerm(expr.getRightOp());
		return context.mkEq(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformRatNeq(final RatNeqExpr expr) {
		final com.microsoft.z3.Expr leftOpTerm = toTerm(expr.getLeftOp());
		final com.microsoft.z3.Expr rightOpTerm = toTerm(expr.getRightOp());
		return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
	}

	private com.microsoft.z3.Expr transformRatGeq(final RatGeqExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkGe(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformRatGt(final RatGtExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkGt(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformRatLeq(final RatLeqExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkLe(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformRatLt(final RatLtExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkLt(leftOpTerm, rightOpTerm);
	}

	/*
	 * Integers
	 */

	private com.microsoft.z3.Expr transformIntLit(final IntLitExpr expr) {
		return context.mkInt(expr.getValue());
	}

	private com.microsoft.z3.Expr transformIntAdd(final IntAddExpr expr) {
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(e -> toTerm(e))
				.toArray(size -> new com.microsoft.z3.ArithExpr[size]);
		return context.mkAdd(opTerms);
	}

	private com.microsoft.z3.Expr transformIntSub(final IntSubExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkSub(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformIntNeg(final IntNegExpr expr) {
		final com.microsoft.z3.ArithExpr opTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getOp());
		return context.mkUnaryMinus(opTerm);
	}

	private com.microsoft.z3.Expr transformIntMul(final IntMulExpr expr) {
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(e -> toTerm(e))
				.toArray(size -> new com.microsoft.z3.ArithExpr[size]);
		return context.mkMul(opTerms);
	}

	private com.microsoft.z3.Expr transformIntDiv(final IntDivExpr expr) {
		final com.microsoft.z3.IntExpr leftOpTerm = (com.microsoft.z3.IntExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.IntExpr rightOpTerm = (com.microsoft.z3.IntExpr) toTerm(expr.getRightOp());
		return context.mkDiv(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformMod(final ModExpr expr) {
		final com.microsoft.z3.IntExpr leftOpTerm = (com.microsoft.z3.IntExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.IntExpr rightOpTerm = (com.microsoft.z3.IntExpr) toTerm(expr.getRightOp());
		return context.mkMod(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformRem(final RemExpr expr) {
		final com.microsoft.z3.IntExpr leftOpTerm = (com.microsoft.z3.IntExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.IntExpr rightOpTerm = (com.microsoft.z3.IntExpr) toTerm(expr.getRightOp());
		return context.mkRem(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformIntEq(final IntEqExpr expr) {
		final com.microsoft.z3.Expr leftOpTerm = toTerm(expr.getLeftOp());
		final com.microsoft.z3.Expr rightOpTerm = toTerm(expr.getRightOp());
		return context.mkEq(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformIntNeq(final IntNeqExpr expr) {
		final com.microsoft.z3.Expr leftOpTerm = toTerm(expr.getLeftOp());
		final com.microsoft.z3.Expr rightOpTerm = toTerm(expr.getRightOp());
		return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
	}

	private com.microsoft.z3.Expr transformIntGeq(final IntGeqExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkGe(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformIntGt(final IntGtExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkGt(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformIntLeq(final IntLeqExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkLe(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformIntLt(final IntLtExpr expr) {
		final com.microsoft.z3.ArithExpr leftOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.ArithExpr rightOpTerm = (com.microsoft.z3.ArithExpr) toTerm(expr.getRightOp());
		return context.mkLt(leftOpTerm, rightOpTerm);
	}

}
