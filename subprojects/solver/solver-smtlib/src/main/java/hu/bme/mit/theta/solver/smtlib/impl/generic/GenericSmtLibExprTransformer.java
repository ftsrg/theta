/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.solver.smtlib.impl.generic;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import com.google.common.collect.ImmutableList;
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
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
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
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvConcatExpr;
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvPosExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
import hu.bme.mit.theta.core.type.fptype.FpAbsExpr;
import hu.bme.mit.theta.core.type.fptype.FpAddExpr;
import hu.bme.mit.theta.core.type.fptype.FpAssignExpr;
import hu.bme.mit.theta.core.type.fptype.FpDivExpr;
import hu.bme.mit.theta.core.type.fptype.FpEqExpr;
import hu.bme.mit.theta.core.type.fptype.FpFromBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpGeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpGtExpr;
import hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr;
import hu.bme.mit.theta.core.type.fptype.FpIsNanExpr;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpLtExpr;
import hu.bme.mit.theta.core.type.fptype.FpMaxExpr;
import hu.bme.mit.theta.core.type.fptype.FpMinExpr;
import hu.bme.mit.theta.core.type.fptype.FpMulExpr;
import hu.bme.mit.theta.core.type.fptype.FpNegExpr;
import hu.bme.mit.theta.core.type.fptype.FpNeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpPosExpr;
import hu.bme.mit.theta.core.type.fptype.FpRemExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpSqrtExpr;
import hu.bme.mit.theta.core.type.fptype.FpSubExpr;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
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
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntPosExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
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
import hu.bme.mit.theta.core.type.rattype.RatPosExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
import hu.bme.mit.theta.core.type.rattype.RatToIntExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibExprTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;

import java.math.BigInteger;
import java.util.List;
import java.util.concurrent.ExecutionException;

public class GenericSmtLibExprTransformer implements SmtLibExprTransformer {
	private static final int CACHE_SIZE = 1000;

	private final SmtLibTransformationManager transformer;

	private final Cache<Expr<?>, String> exprToTerm;
	private final DispatchTable<String> table;
	private final Env env;

	public GenericSmtLibExprTransformer(final SmtLibTransformationManager transformer) {
		this.transformer = transformer;
		this.env = new Env();

		this.exprToTerm = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

		this.table = DispatchTable.<String>builder()

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

				.addCase(RatPosExpr.class, this::transformRatPos)

				.addCase(RatNegExpr.class, this::transformRatNeg)

				.addCase(RatMulExpr.class, this::transformRatMul)

				.addCase(RatDivExpr.class, this::transformRatDiv)

				.addCase(RatEqExpr.class, this::transformRatEq)

				.addCase(RatNeqExpr.class, this::transformRatNeq)

				.addCase(RatGeqExpr.class, this::transformRatGeq)

				.addCase(RatGtExpr.class, this::transformRatGt)

				.addCase(RatLeqExpr.class, this::transformRatLeq)

				.addCase(RatLtExpr.class, this::transformRatLt)

				.addCase(RatToIntExpr.class, this::transformRatToInt)

				// Integers

				.addCase(IntLitExpr.class, this::transformIntLit)

				.addCase(IntAddExpr.class, this::transformIntAdd)

				.addCase(IntSubExpr.class, this::transformIntSub)

				.addCase(IntPosExpr.class, this::transformIntPos)

				.addCase(IntNegExpr.class, this::transformIntNeg)

				.addCase(IntMulExpr.class, this::transformIntMul)

				.addCase(IntDivExpr.class, this::transformIntDiv)

				.addCase(IntModExpr.class, this::transformIntMod)

				.addCase(IntRemExpr.class, this::transformIntRem)

				.addCase(IntEqExpr.class, this::transformIntEq)

				.addCase(IntNeqExpr.class, this::transformIntNeq)

				.addCase(IntGeqExpr.class, this::transformIntGeq)

				.addCase(IntGtExpr.class, this::transformIntGt)

				.addCase(IntLeqExpr.class, this::transformIntLeq)

				.addCase(IntLtExpr.class, this::transformIntLt)

				.addCase(IntToRatExpr.class, this::transformIntToRat)

				// Bitvectors

				.addCase(BvLitExpr.class, this::transformBvLit)

				.addCase(BvConcatExpr.class, this::transformBvConcat)

				.addCase(BvExtractExpr.class, this::transformBvExtract)

				.addCase(BvZExtExpr.class, this::transformBvZExt)

				.addCase(BvSExtExpr.class, this::transformBvSExt)

				.addCase(BvAddExpr.class, this::transformBvAdd)

				.addCase(BvSubExpr.class, this::transformBvSub)

				.addCase(BvPosExpr.class, this::transformBvPos)

				.addCase(BvNegExpr.class, this::transformBvNeg)

				.addCase(BvMulExpr.class, this::transformBvMul)

				.addCase(BvUDivExpr.class, this::transformBvUDiv)

				.addCase(BvSDivExpr.class, this::transformBvSDiv)

				.addCase(BvSModExpr.class, this::transformBvSMod)

				.addCase(BvURemExpr.class, this::transformBvURem)

				.addCase(BvSRemExpr.class, this::transformBvSRem)

				.addCase(BvAndExpr.class, this::transformBvAnd)

				.addCase(BvOrExpr.class, this::transformBvOr)

				.addCase(BvXorExpr.class, this::transformBvXor)

				.addCase(BvNotExpr.class, this::transformBvNot)

				.addCase(BvShiftLeftExpr.class, this::transformBvShiftLeft)

				.addCase(BvArithShiftRightExpr.class, this::transformBvArithShiftRight)

				.addCase(BvLogicShiftRightExpr.class, this::transformBvLogicShiftRight)

				.addCase(BvRotateLeftExpr.class, this::transformBvRotateLeft)

				.addCase(BvRotateRightExpr.class, this::transformBvRotateRight)

				.addCase(BvEqExpr.class, this::transformBvEq)

				.addCase(BvNeqExpr.class, this::transformBvNeq)

				.addCase(BvUGeqExpr.class, this::transformBvUGeq)

				.addCase(BvUGtExpr.class, this::transformBvUGt)

				.addCase(BvULeqExpr.class, this::transformBvULeq)

				.addCase(BvULtExpr.class, this::transformBvULt)

				.addCase(BvSGeqExpr.class, this::transformBvSGeq)

				.addCase(BvSGtExpr.class, this::transformBvSGt)

				.addCase(BvSLeqExpr.class, this::transformBvSLeq)

				.addCase(BvSLtExpr.class, this::transformBvSLt)

				// Floating points

				.addCase(FpLitExpr.class, this::transformFpLit)

				.addCase(FpAddExpr.class, this::transformFpAdd)

				.addCase(FpSubExpr.class, this::transformFpSub)

				.addCase(FpPosExpr.class, this::transformFpPos)

				.addCase(FpNegExpr.class, this::transformFpNeg)

				.addCase(FpMulExpr.class, this::transformFpMul)

				.addCase(FpDivExpr.class, this::transformFpDiv)

				.addCase(FpEqExpr.class, this::transformFpEq)

				.addCase(FpAssignExpr.class, this::transformFpAssign)

				.addCase(FpGeqExpr.class, this::transformFpGeq)

				.addCase(FpLeqExpr.class, this::transformFpLeq)

				.addCase(FpGtExpr.class, this::transformFpGt)

				.addCase(FpLtExpr.class, this::transformFpLt)

				.addCase(FpNeqExpr.class, this::transformFpNeq)

				.addCase(FpAbsExpr.class, this::transformFpAbs)

				.addCase(FpRoundToIntegralExpr.class, this::transformFpRoundToIntegral)

				.addCase(FpMaxExpr.class, this::transformFpMax)

				.addCase(FpMinExpr.class, this::transformFpMin)

				.addCase(FpSqrtExpr.class, this::transformFpSqrt)

				.addCase(FpRemExpr.class, this::transformFpRem)

				.addCase(FpIsNanExpr.class, this::transformFpIsNaN)

				.addCase(FpIsInfiniteExpr.class, this::transformFpIsInfinite)

				.addCase(FpFromBvExpr.class, this::transformFpFromBv)

				.addCase(FpToBvExpr.class, this::transformFpToBv)

				.addCase(FpToFpExpr.class, this::transformFpToFp)

				// Functions

				.addCase(FuncAppExpr.class, this::transformFuncApp)

				// Arrays

				.addCase(ArrayReadExpr.class, this::transformArrayRead)

				.addCase(ArrayWriteExpr.class, this::transformArrayWrite)

				.addCase(ArrayEqExpr.class, this::transformArrayEq)

				.addCase(ArrayNeqExpr.class, this::transformArrayNeq)

				.addCase(ArrayLitExpr.class, this::transformArrayLit)

				.addCase(ArrayInitExpr.class, this::transformArrayInit)

				.build();
	}

	@Override
	public final String toTerm(final Expr<?> expr) {
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

	protected String transformRef(final RefExpr<?> expr) {
		final Decl<?> decl = expr.getDecl();
		if (decl instanceof ConstDecl) {
			return transformer.toSymbol(decl);
		} else if (decl instanceof ParamDecl) {
			return (String) env.eval(DeclSymbol.of(decl));
		} else {
			throw new UnsupportedOperationException("Cannot transform reference for declaration: " + decl);
		}
	}

	protected String transformIte(final IteExpr<?> expr) {
		final String condTerm = toTerm(expr.getCond());
		final String thenTerm = toTerm(expr.getThen());
		final String elzeTerm = toTerm(expr.getElse());
		return String.format("(ite %s %s %s)", condTerm, thenTerm, elzeTerm);
	}

	/*
	 * Booleans
	 */

	protected String transformFalse(final FalseExpr expr) {
		return "false";
	}

	protected String transformTrue(final TrueExpr expr) {
		return "true";
	}

	protected String transformNot(final NotExpr expr) {
		return String.format("(not %s)", toTerm(expr.getOp()));
	}

	protected String transformImply(final ImplyExpr expr) {
		return String.format("(=> %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIff(final IffExpr expr) {
		return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformXor(final XorExpr expr) {
		return String.format("(xor %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformAnd(final AndExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return "true";
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(and %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(and %s %s)", op1, op2)
					);
		}
	}

	protected String transformOr(final OrExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return "false";
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(or %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(or %s %s)", op1, op2)
					);
		}
	}

	protected String transformExists(final ExistsExpr expr) {
		env.push();
		final String[] paramTerms = transformParamDecls(expr.getParamDecls());
		final String opTerm = toTerm(expr.getOp());
		final String result = String.format("(exists (%s) %s)", String.join(" ", paramTerms), opTerm);
		env.pop();
		return result;
	}

	protected String transformForall(final ForallExpr expr) {
		env.push();
		final String[] paramTerms = transformParamDecls(expr.getParamDecls());
		final String opTerm = toTerm(expr.getOp());
		final String result = String.format("(forall (%s) %s)", String.join(" ", paramTerms), opTerm);
		env.pop();
		return result;
	}

	private String[] transformParamDecls(final List<ParamDecl<?>> paramDecls) {
		final String[] paramTerms = new String[paramDecls.size()];
		int i = 0;
		for (final ParamDecl<?> paramDecl : paramDecls) {
			final String paramSymbol = transformParamDecl(paramDecl);
			paramTerms[i] = paramSymbol;
			env.define(DeclSymbol.of(paramDecl), paramDecl.getName());
			i++;
		}
		return paramTerms;
	}

	private String transformParamDecl(final ParamDecl<?> paramDecl) {
		final Type type = paramDecl.getType();
		if (type instanceof FuncType<?, ?>) {
			throw new UnsupportedOperationException("Only simple types are supported");
		} else {
			return String.format("(%s %s)", paramDecl.getName(), transformer.toSort(type));
		}
	}

	/*
	 * Rationals
	 */

	protected String transformRatLit(final RatLitExpr expr) {
		return String.format("(/ %d.0 %d.0)", expr.getNum(), expr.getDenom());
	}

	protected String transformRatAdd(final RatAddExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return "0.0";
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(+ %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(+ %s %s)", op1, op2)
					);
		}
	}

	protected String transformRatSub(final RatSubExpr expr) {
		return String.format("(- %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatPos(final RatPosExpr expr) {
		return toTerm(expr.getOp());
	}

	protected String transformRatNeg(final RatNegExpr expr) {
		return String.format("(- %s)", toTerm(expr.getOp()));
	}

	protected String transformRatMul(final RatMulExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return "1.0";
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(* %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(* %s %s)", op1, op2)
					);
		}
	}

	protected String transformRatDiv(final RatDivExpr expr) {
		return String.format("(/ %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatEq(final RatEqExpr expr) {
		return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatNeq(final RatNeqExpr expr) {
		return String.format("(not (= %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatGeq(final RatGeqExpr expr) {
		return String.format("(>= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatGt(final RatGtExpr expr) {
		return String.format("(> %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatLeq(final RatLeqExpr expr) {
		return String.format("(<= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatLt(final RatLtExpr expr) {
		return String.format("(< %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformRatToInt(final RatToIntExpr expr) {
		return String.format("(to_int %s)", toTerm(expr.getOp()));
	}

	/*
	 * Integers
	 */

	protected String transformIntLit(final IntLitExpr expr) {
		if (expr.getValue().compareTo(BigInteger.ZERO) < 0) {
			return String.format("(- %s)", expr.getValue().abs());
		} else {
			return expr.getValue().toString();
		}
	}

	protected String transformIntAdd(final IntAddExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return "0";
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(+ %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(+ %s %s)", op1, op2)
					);
		}
	}

	protected String transformIntSub(final IntSubExpr expr) {
		return String.format("(- %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntPos(final IntPosExpr expr) {
		return toTerm(expr.getOp());
	}

	protected String transformIntNeg(final IntNegExpr expr) {
		return String.format("(- %s)", toTerm(expr.getOp()));
	}

	protected String transformIntMul(final IntMulExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return "1";
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(* %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(* %s %s)", op1, op2)
					);
		}
	}

	protected String transformIntDiv(final IntDivExpr expr) {
		return String.format("(div %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntMod(final IntModExpr expr) {
		return String.format("(mod %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntRem(final IntRemExpr expr) {
		return String.format("(rem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntEq(final IntEqExpr expr) {
		return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntNeq(final IntNeqExpr expr) {
		return String.format("(not (= %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntGeq(final IntGeqExpr expr) {
		return String.format("(>= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntGt(final IntGtExpr expr) {
		return String.format("(> %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntLeq(final IntLeqExpr expr) {
		return String.format("(<= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntLt(final IntLtExpr expr) {
		return String.format("(< %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformIntToRat(final IntToRatExpr expr) {
		return String.format("(to_real %s)", toTerm(expr.getOp()));
	}

	/*
	 * Bitvectors
	 */

	protected String transformBvLit(final BvLitExpr expr) {
		final StringBuilder sb = new StringBuilder(expr.getType().getSize() + 1);

		for (boolean value : expr.getValue()) {
			sb.append(value ? "1" : "0");
		}

		return String.format("#b%s", sb);
	}

	protected String transformBvConcat(final BvConcatExpr expr) {
		final String[] opTerms = expr.getOps().stream()
				.map(this::toTerm)
				.toArray(String[]::new);

		return String.format("(concat %s)", String.join(" ", opTerms));
	}

	protected String transformBvExtract(final BvExtractExpr expr) {
		final var until = expr.getUntil().getValue().subtract(BigInteger.ONE);
		final var from = expr.getFrom().getValue();

		return String.format("((_ extract %s %s) %s)", until, from, toTerm(expr.getBitvec()));
	}

	protected String transformBvZExt(final BvZExtExpr expr) {
		final var extendWith = expr.getExtendType().getSize() - expr.getOp().getType().getSize();
		return String.format("((_ zero_extend %d) %s)", extendWith, toTerm(expr.getOp()));
	}

	protected String transformBvSExt(final BvSExtExpr expr) {
		final var extendWith = expr.getExtendType().getSize() - expr.getOp().getType().getSize();
		return String.format("((_ sign_extend %d) %s)", extendWith, toTerm(expr.getOp()));
	}

	protected String transformBvAdd(final BvAddExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return toTerm(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, expr.getType().getSize()));
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(bvadd %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(bvadd %s %s)", op1, op2)
					);
		}
	}

	protected String transformBvSub(final BvSubExpr expr) {
		return String.format("(bvsub %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvPos(final BvPosExpr expr) {
		return toTerm(expr.getOp());
	}

	protected String transformBvNeg(final BvNegExpr expr) {
		return String.format("(bvneg %s)", toTerm(expr.getOp()));
	}

	protected String transformBvMul(final BvMulExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return toTerm(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ONE, expr.getType().getSize()));
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(bvmul %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(bvmul %s %s)", op1, op2)
					);
		}
	}

	protected String transformBvUDiv(final BvUDivExpr expr) {
		return String.format("(bvudiv %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvSDiv(final BvSDivExpr expr) {
		return String.format("(bvsdiv %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvSMod(final BvSModExpr expr) {
		return String.format("(bvsmod %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvURem(final BvURemExpr expr) {
		return String.format("(bvurem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvSRem(final BvSRemExpr expr) {
		return String.format("(bvsrem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvAnd(final BvAndExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return toTerm(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.TWO.pow(expr.getType().getSize()).subtract(BigInteger.ONE), expr.getType().getSize()));
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(bvand %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(bvand %s %s)", op1, op2)
					);
		}
	}

	protected String transformBvOr(final BvOrExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return toTerm(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, expr.getType().getSize()));
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(bvor %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(bvor %s %s)", op1, op2)
					);
		}
	}

	protected String transformBvXor(final BvXorExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return toTerm(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, expr.getType().getSize()));
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(bvxor %s %s)", acc, toTerm(op)),
							(op1, op2) -> String.format("(bvxor %s %s)", op1, op2)
					);
		}
	}

	protected String transformBvNot(final BvNotExpr expr) {
		return String.format("(bvnot %s)", toTerm(expr.getOp()));
	}

	protected String transformBvShiftLeft(final BvShiftLeftExpr expr) {
		return String.format("(bvshl %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvArithShiftRight(final BvArithShiftRightExpr expr) {
		return String.format("(bvashr %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvLogicShiftRight(final BvLogicShiftRightExpr expr) {
		return String.format("(bvlshr %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvRotateLeft(final BvRotateLeftExpr expr) {
		final var toRotate = toTerm(expr.getLeftOp());
		final var rotateWith = toTerm(expr.getRightOp());
		final var size = toTerm(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(expr.getType().getSize()), expr.getType().getSize()));
		return String.format("(bvor (bvshl %s %s) (bvlshr %s (bvsub %s %s)))", toRotate, rotateWith, toRotate, size, rotateWith);
	}

	protected String transformBvRotateRight(final BvRotateRightExpr expr) {
		final var toRotate = toTerm(expr.getLeftOp());
		final var rotateWith = toTerm(expr.getRightOp());
		final var size = toTerm(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(expr.getType().getSize()), expr.getType().getSize()));
		return String.format("(bvor (bvlshr %s %s) (bvshl %s (bvsub %s %s)))", toRotate, rotateWith, toRotate, size, rotateWith);
	}

	protected String transformBvEq(final BvEqExpr expr) {
		return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvNeq(final BvNeqExpr expr) {
		return String.format("(not (= %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvUGeq(final BvUGeqExpr expr) {
		return String.format("(bvuge %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvUGt(final BvUGtExpr expr) {
		return String.format("(bvugt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvULeq(final BvULeqExpr expr) {
		return String.format("(bvule %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvULt(final BvULtExpr expr) {
		return String.format("(bvult %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvSGeq(final BvSGeqExpr expr) {
		return String.format("(bvsge %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvSGt(final BvSGtExpr expr) {
		return String.format("(bvsgt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvSLeq(final BvSLeqExpr expr) {
		return String.format("(bvsle %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformBvSLt(final BvSLtExpr expr) {
		return String.format("(bvslt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	/*
	 * Floating points
	 */

	protected String transformFpLit(final FpLitExpr expr) {
		return String.format("(fp #b%s  #b%s #b%s)",
				expr.getHidden() ? "1" : "0",
				transformBvLit(expr.getExponent()).substring(2),
				transformBvLit(expr.getSignificand()).substring(2)
		);
	}

	protected String transformFpAdd(final FpAddExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return String.format("(_ +zero %d %d)", expr.getType().getExponent(), expr.getType().getSignificand());
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(fp.add %s %s %s)", transformFpRoundingMode(expr.getRoundingMode()), acc, toTerm(op)),
							(op1, op2) -> String.format("(fp.add %s %s %s)", transformFpRoundingMode(expr.getRoundingMode()), op1, op2)
					);
		}
	}

	protected String transformFpSub(final FpSubExpr expr) {
		return String.format("(fp.sub %s %s %s)", transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpPos(final FpPosExpr expr) {
		return toTerm(expr.getOp());
	}

	protected String transformFpNeg(final FpNegExpr expr) {
		return String.format("(fp.neg %s)", toTerm(expr.getOp()));
	}

	protected String transformFpMul(final FpMulExpr expr) {
		if (expr.getArity() == 1) {
			return toTerm(expr.getOps().get(0));
		} else if (expr.getArity() == 0) {
			return String.format("(fp #b0 #b0%s #b%s)", "1".repeat(expr.getType().getExponent() - 1), "0".repeat(expr.getType().getSignificand()));
		} else {
			return expr.getOps().stream().skip(1)
					.reduce(
							toTerm(expr.getOps().get(0)),
							(acc, op) -> String.format("(fp.mul %s %s %s)", transformFpRoundingMode(expr.getRoundingMode()), acc, toTerm(op)),
							(op1, op2) -> String.format("(fp.mul %s %s %s)", transformFpRoundingMode(expr.getRoundingMode()), op1, op2)
					);
		}
	}

	protected String transformFpDiv(final FpDivExpr expr) {
		return String.format("(fp.div %s %s %s)", transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpEq(final FpEqExpr expr) {
		return String.format("(fp.eq %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpAssign(final FpAssignExpr expr) {
		return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpNeq(final FpNeqExpr expr) {
		return String.format("(not (fp.eq %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpGeq(final FpGeqExpr expr) {
		return String.format("(fp.geq %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpGt(final FpGtExpr expr) {
		return String.format("(fp.gt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpLeq(final FpLeqExpr expr) {
		return String.format("(fp.leq %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpLt(final FpLtExpr expr) {
		return String.format("(fp.lt %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpAbs(final FpAbsExpr expr) {
		return String.format("(fp.abs %s)", toTerm(expr.getOp()));
	}

	protected String transformFpRoundToIntegral(final FpRoundToIntegralExpr expr) {
		return String.format("(fp.roundToIntegral %s %s)", transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getOp()));
	}

	protected String transformFpMin(final FpMinExpr expr) {
		return String.format("(fp.min %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpMax(final FpMaxExpr expr) {
		return String.format("(fp.max %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpSqrt(final FpSqrtExpr expr) {
		return String.format("(fp.sqrt %s %s)", transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getOp()));
	}

	protected String transformFpRem(final FpRemExpr expr) {
		return String.format("(fp.rem %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformFpIsNaN(final FpIsNanExpr expr) {
		return String.format("(fp.isNaN %s)", toTerm(expr.getOp()));
	}

	protected String transformFpIsInfinite(final FpIsInfiniteExpr expr) {
		return String.format("(fp.isInfinite %s)", toTerm(expr.getOp()));
	}

	protected String transformFpFromBv(final FpFromBvExpr expr) {
		if (expr.isSigned()) {
			return String.format("((_ to_fp %d %d) %s %s)", expr.getType().getExponent(), expr.getType().getSignificand(), transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getOp()));
		} else {
			return String.format("((_ to_fp_unsigned %d %d) %s %s)", expr.getType().getExponent(), expr.getType().getSignificand(), transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getOp()));
		}
	}

	protected String transformFpToBv(final FpToBvExpr expr) {
		if (expr.getSgn()) {
			return String.format("((_ fp.to_sbv %d) %s %s) ", expr.getType().getSize(), transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getOp()));
		} else {
			return String.format("((_ fp.to_ubv %d) %s %s) ", expr.getType().getSize(), transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getOp()));
		}
	}

	protected String transformFpToFp(final FpToFpExpr expr) {
		return String.format("((_ to_fp %d %d) %s %s)", expr.getType().getExponent(), expr.getType().getSignificand(), transformFpRoundingMode(expr.getRoundingMode()), toTerm(expr.getOp()));
	}

	private String transformFpRoundingMode(FpRoundingMode roundingMode) {
		switch (roundingMode) {
			case RNE:
				return "RNE";
			case RNA:
				return "RNA";
			case RTP:
				return "RTP";
			case RTN:
				return "RTN";
			case RTZ:
				return "RTZ";
			default:
				throw new UnsupportedOperationException();
		}
	}

	/*
	 * Functions
	 */

	protected String transformFuncApp(final FuncAppExpr<?, ?> expr) {
		final Tuple2<Expr<?>, List<Expr<?>>> funcAndArgs = extractFuncAndArgs(expr);
		final Expr<?> func = funcAndArgs.get1();
		if (func instanceof RefExpr) {
			final RefExpr<?> ref = (RefExpr<?>) func;
			final Decl<?> decl = ref.getDecl();
			final String funcDecl = transformer.toSymbol(decl);
			final List<Expr<?>> args = funcAndArgs.get2();
			final String[] argTerms = args.stream()
					.map(this::toTerm)
					.toArray(String[]::new);

			return String.format("(%s %s)", funcDecl, String.join(" ", argTerms));
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

	/*
	 * Arrays
	 */

	protected String transformArrayRead(final ArrayReadExpr<?, ?> expr) {
		return String.format("(select %s %s)", toTerm(expr.getArray()), toTerm(expr.getIndex()));
	}

	protected String transformArrayWrite(final ArrayWriteExpr<?, ?> expr) {
		return String.format("(store %s %s %s)", toTerm(expr.getArray()), toTerm(expr.getIndex()), toTerm(expr.getElem()));
	}

	protected String transformArrayEq(final ArrayEqExpr<?, ?> expr) {
		return String.format("(= %s %s)", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformArrayNeq(final ArrayNeqExpr<?, ?> expr) {
		return String.format("(not (= %s %s))", toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
	}

	protected String transformArrayLit(final ArrayLitExpr<?, ?> expr) {
		String running = String.format("((as const %s) %s)", transformer.toSort(expr.getType()), toTerm(expr.getElseElem()));
		for (Tuple2<? extends Expr<?>, ? extends Expr<?>> elem : expr.getElements()) {
			running = String.format("(store %s %s %s)", running, toTerm(elem.get1()), toTerm(elem.get2()));
		}
		return running;
	}

	protected String transformArrayInit(final ArrayInitExpr<?, ?> expr) {
		String running = String.format("((as const %s) %s)", transformer.toSort(expr.getType()), toTerm(expr.getElseElem()));
		for (Tuple2<? extends Expr<?>, ? extends Expr<?>> elem : expr.getElements()) {
			running = String.format("(store %s %s %s)", running, toTerm(elem.get1()), toTerm(elem.get2()));
		}
		return running;
	}
}
