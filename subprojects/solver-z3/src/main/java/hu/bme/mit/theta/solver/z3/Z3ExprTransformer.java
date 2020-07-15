/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.solver.z3;

import java.util.List;
import java.util.concurrent.ExecutionException;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import com.google.common.collect.ImmutableList;
import com.microsoft.z3.Context;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayEqExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayNeqExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
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
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
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

final class Z3ExprTransformer {

	private static final int CACHE_SIZE = 1000;

	private final Z3TransformationManager transformer;
	private final Context context;

	private final Cache<Expr<?>, com.microsoft.z3.Expr> exprToTerm;
	private final DispatchTable<com.microsoft.z3.Expr> table;
	private final Env env;

	public Z3ExprTransformer(final Z3TransformationManager transformer, final Context context) {
		this.context = context;
		this.transformer = transformer;
		this.env = new Env();

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

				.addCase(XorExpr.class, this::transformXor)

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

				.addCase(IntToRatExpr.class, this::transformIntToRat)

				// Functions

				.addCase(FuncAppExpr.class, this::transformFuncApp)

				// Arrays

				.addCase(ArrayReadExpr.class, this::transformArrayRead)

				.addCase(ArrayWriteExpr.class, this::transformArrayWrite)

				.addCase(ArrayEqExpr.class, this::transformArrayEq)

				.addCase(ArrayNeqExpr.class, this::transformArrayNeq)

				.addCase(ArrayLitExpr.class, this::transformArrayLit)

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
		if (decl instanceof ConstDecl) {
			final com.microsoft.z3.FuncDecl funcDecl = transformer.toSymbol(decl);
			return context.mkConst(funcDecl);
		} else if (decl instanceof ParamDecl) {
			final com.microsoft.z3.FuncDecl funcDecl = (com.microsoft.z3.FuncDecl) env.eval(DeclSymbol.of(decl));
			return context.mkConst(funcDecl);
		} else {
			throw new UnsupportedOperationException("Cannot transform reference for declaration: " + decl);
		}
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

	private com.microsoft.z3.Expr transformXor(final XorExpr expr) {
		final com.microsoft.z3.BoolExpr leftOpTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getLeftOp());
		final com.microsoft.z3.BoolExpr rightOpTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getRightOp());
		return context.mkXor(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformAnd(final AndExpr expr) {
		final com.microsoft.z3.BoolExpr[] opTerms = expr.getOps().stream().map(this::toTerm)
				.toArray(size -> new com.microsoft.z3.BoolExpr[size]);
		return context.mkAnd(opTerms);
	}

	private com.microsoft.z3.Expr transformOr(final OrExpr expr) {
		final com.microsoft.z3.BoolExpr[] opTerms = expr.getOps().stream().map(this::toTerm)
				.toArray(size -> new com.microsoft.z3.BoolExpr[size]);
		return context.mkOr(opTerms);
	}

	private com.microsoft.z3.Expr transformExists(final ExistsExpr expr) {
		env.push();
		final com.microsoft.z3.Expr[] paramTerms = transformParamDecls(expr.getParamDecls());
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getOp());
		final com.microsoft.z3.BoolExpr result = context.mkExists(paramTerms, opTerm, 1, null, null, null, null);
		env.pop();
		return result;
	}

	private com.microsoft.z3.Expr transformForall(final ForallExpr expr) {
		env.push();
		final com.microsoft.z3.Expr[] paramTerms = transformParamDecls(expr.getParamDecls());
		final com.microsoft.z3.BoolExpr opTerm = (com.microsoft.z3.BoolExpr) toTerm(expr.getOp());
		final com.microsoft.z3.BoolExpr result = context.mkForall(paramTerms, opTerm, 1, null, null, null, null);
		env.pop();
		return result;
	}

	private com.microsoft.z3.Expr[] transformParamDecls(final List<ParamDecl<?>> paramDecls) {
		final com.microsoft.z3.Expr[] paramTerms = new com.microsoft.z3.Expr[paramDecls.size()];
		int i = 0;
		for (final ParamDecl<?> paramDecl : paramDecls) {
			final com.microsoft.z3.FuncDecl paramSymbol = transformParamDecl(paramDecl);
			paramTerms[i] = context.mkConst(paramSymbol);
			env.define(DeclSymbol.of(paramDecl), paramSymbol);
			i++;
		}
		return paramTerms;
	}

	private com.microsoft.z3.FuncDecl transformParamDecl(final ParamDecl<?> paramDecl) {
		final Type type = paramDecl.getType();
		if (type instanceof FuncType<?, ?>) {
			throw new UnsupportedOperationException("Only simple types are supported");
		} else {
			final com.microsoft.z3.Sort sort = transformer.toSort(type);
			return context.mkConstDecl(paramDecl.getName(), sort);
		}
	}

	/*
	 * Rationals
	 */

	private com.microsoft.z3.Expr transformRatLit(final RatLitExpr expr) {
		return context.mkReal(Math.toIntExact(expr.getNum()), Math.toIntExact(expr.getDenom()));
	}

	private com.microsoft.z3.Expr transformRatAdd(final RatAddExpr expr) {
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(this::toTerm)
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
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(this::toTerm)
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
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(this::toTerm)
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
		final com.microsoft.z3.ArithExpr[] opTerms = expr.getOps().stream().map(this::toTerm)
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

	private com.microsoft.z3.Expr transformIntToRat(final IntToRatExpr expr) {
		final com.microsoft.z3.IntExpr opTerm = (com.microsoft.z3.IntExpr) toTerm(expr.getOp());
		return context.mkInt2Real(opTerm);
	}

	/*
	 * Arrays
	 */

	private com.microsoft.z3.Expr transformArrayRead(final ArrayReadExpr<?, ?> expr) {
		final com.microsoft.z3.ArrayExpr arrayTerm = (com.microsoft.z3.ArrayExpr) toTerm(expr.getArray());
		final com.microsoft.z3.Expr indexTerm = toTerm(expr.getIndex());
		return context.mkSelect(arrayTerm, indexTerm);
	}

	private com.microsoft.z3.Expr transformArrayWrite(final ArrayWriteExpr<?, ?> expr) {
		final com.microsoft.z3.ArrayExpr arrayTerm = (com.microsoft.z3.ArrayExpr) toTerm(expr.getArray());
		final com.microsoft.z3.Expr indexTerm = toTerm(expr.getIndex());
		final com.microsoft.z3.Expr elemTerm = toTerm(expr.getElem());
		return context.mkStore(arrayTerm, indexTerm, elemTerm);
	}

	private com.microsoft.z3.Expr transformArrayEq(final ArrayEqExpr<?, ?> expr) {
		final com.microsoft.z3.Expr leftOpTerm = toTerm(expr.getLeftOp());
		final com.microsoft.z3.Expr rightOpTerm = toTerm(expr.getRightOp());
		return context.mkEq(leftOpTerm, rightOpTerm);
	}

	private com.microsoft.z3.Expr transformArrayNeq(final ArrayNeqExpr<?, ?> expr) {
		final com.microsoft.z3.Expr leftOpTerm = toTerm(expr.getLeftOp());
		final com.microsoft.z3.Expr rightOpTerm = toTerm(expr.getRightOp());
		return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
	}

	private com.microsoft.z3.Expr transformArrayLit(final ArrayLitExpr<?, ?> expr) {
		com.microsoft.z3.ArrayExpr running = context.mkConstArray(transformer.toSort(expr.getElseElem().getType()), toTerm(expr.getElseElem()));
		for (Tuple2<? extends Expr<?>, ? extends Expr<?>> elem : expr.getElements()) {
			running = context.mkStore(running, toTerm(elem.get1()), toTerm(elem.get2()));
		}
		return running;
	}

	/*
	 * Functions
	 */

	private com.microsoft.z3.Expr transformFuncApp(final FuncAppExpr<?, ?> expr) {
		final Tuple2<Expr<?>, List<Expr<?>>> funcAndArgs = extractFuncAndArgs(expr);
		final Expr<?> func = funcAndArgs.get1();
		if (func instanceof RefExpr) {
			final RefExpr<?> ref = (RefExpr<?>) func;
			final Decl<?> decl = ref.getDecl();
			final com.microsoft.z3.FuncDecl funcDecl = transformer.toSymbol(decl);
			final List<Expr<?>> args = funcAndArgs.get2();
			final com.microsoft.z3.Expr[] argTerms = args.stream().map(this::toTerm)
					.toArray(size -> new com.microsoft.z3.Expr[size]);
			return context.mkApp(funcDecl, argTerms);
		} else {
			throw new UnsupportedOperationException("Higher order functions are not supported: " + func);
		}
	}

	private static Tuple2<Expr<?>, List<Expr<?>>> extractFuncAndArgs(final FuncAppExpr<?, ?> expr) {
		final Expr<?> func = expr.getFunc();
		final Expr<?> arg = expr.getParam();
		if (func instanceof FuncAppExpr) {
			final FuncAppExpr<?, ?> funcApp = (FuncAppExpr<?, ?>) func;
			final Tuple2<Expr<?>, List<Expr<?>>> funcAndArgs = extractFuncAndArgs(funcApp);
			final Expr<?> resFunc = funcAndArgs.get1();
			final List<Expr<?>> args = funcAndArgs.get2();
			final List<Expr<?>> resArgs = ImmutableList.<Expr<?>>builder().addAll(args).add(arg).build();
			return Tuple2.of(resFunc, resArgs);
		} else {
			return Tuple2.of(func, ImmutableList.of(arg));
		}
	}

}
