/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.fptype.FpAbsExpr;
import hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr;
import hu.bme.mit.theta.core.type.fptype.FpIsNanExpr;
import hu.bme.mit.theta.core.type.fptype.FpMaxExpr;
import hu.bme.mit.theta.core.type.fptype.FpMinExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpSqrtExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

//TODO: type-right conversions (because sqrt and sqrtf might have different domains)
public class FpFunctionsToExprs extends ProcedurePass {
	private static final Map<String, BiFunction<XcfaProcedure.Builder, XcfaLabel.ProcedureCallXcfaLabel, XcfaLabel>> handlers = new LinkedHashMap<>();
	private static void addHandler(String[] names, BiFunction<XcfaProcedure.Builder, XcfaLabel.ProcedureCallXcfaLabel, XcfaLabel> handler) {
		for (String name : names) {
			handlers.put(name, handler);
		}
	}

	static {
		addHandler(new String[]{"fabs", "fabsf", "fabsl"}, FpFunctionsToExprs::handleFabs);
		addHandler(new String[]{"floor", "floorf", "floorl"}, FpFunctionsToExprs::handleFloor);
		addHandler(new String[]{"fmax", "fmaxf", "fmaxl"}, FpFunctionsToExprs::handleFmax);
		addHandler(new String[]{"fmin", "fminf", "fminl"}, FpFunctionsToExprs::handleFmin);
		addHandler(new String[]{"fmod", "fmodf", "fmodl"}, FpFunctionsToExprs::handleFmod);
		addHandler(new String[]{"sqrt", "sqrtf", "sqrtl"}, FpFunctionsToExprs::handleSqrt);
		addHandler(new String[]{"round", "roundf", "roundl"}, FpFunctionsToExprs::handleRound);
		addHandler(new String[]{"isnan"}, FpFunctionsToExprs::handleIsnan);
		addHandler(new String[]{"trunc"}, FpFunctionsToExprs::handleTrunc);
		addHandler(new String[]{"ceil"}, FpFunctionsToExprs::handleCeil);
		addHandler(new String[]{"isnormal"}, FpFunctionsToExprs::handleIsnormal);
		addHandler(new String[]{"isinf", "__isinf", "__isinff", "__isinfl"}, FpFunctionsToExprs::handleIsinf);
		addHandler(new String[]{"isfinite"}, FpFunctionsToExprs::handleIsfinite);
		addHandler(new String[]{"__fpclassify", "__fpclassifyf", "__fpclassifyl"}, FpFunctionsToExprs::handleFpclassify);
	}

	private static XcfaLabel handleTrunc(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(),
				FpRoundToIntegralExpr.of(FpRoundingMode.RTZ, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}

	private static XcfaLabel handleCeil(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(),
				FpRoundToIntegralExpr.of(FpRoundingMode.RTP, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}

	private static XcfaLabel handleIsinf(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		CComplexType type = CComplexType.getType(expr);
		//noinspection unchecked
		AssignStmt<?> assign = Assign(
				cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), type.getSmtType()),
				cast(Ite(FpIsInfiniteExpr.of((Expr<FpType>) callStmt.getParams().get(1)), type.getUnitValue(), type.getNullValue()), type.getSmtType()));
		FrontendMetadata.create(assign.getExpr(), "cType", type);
		return Stmt(assign);
	}

	private static XcfaLabel handleIsfinite(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		CComplexType type = CComplexType.getType(expr);
		//noinspection unchecked
		AssignStmt<?> assign = Assign(
				cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), type.getSmtType()),
				cast(Ite(Not(FpIsInfiniteExpr.of((Expr<FpType>) callStmt.getParams().get(1))), type.getUnitValue(), type.getNullValue()), type.getSmtType()));
		FrontendMetadata.create(assign.getExpr(), "cType", type);
		return Stmt(assign);
	}

	private static XcfaLabel handleIsnormal(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		throw new UnsupportedOperationException();
	}


	private static XcfaLabel handleFpclassify(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		throw new UnsupportedOperationException();
	}

	private static XcfaLabel handleIsnan(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		CComplexType type = CComplexType.getType(expr);
		//noinspection unchecked
		AssignStmt<?> assign = Assign(
				cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), type.getSmtType()),
				cast(Ite(FpIsNanExpr.of((Expr<FpType>) callStmt.getParams().get(1)), type.getUnitValue(), type.getNullValue()), type.getSmtType()));
		FrontendMetadata.create(assign.getExpr(), "cType", type);
		return Stmt(assign);
	}

	private static XcfaLabel handleRound(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpRoundToIntegralExpr.of(FpRoundingMode.RNA, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}

	private static XcfaLabel handleSqrt(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpSqrtExpr.of(FpRoundingMode.RNE, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}

	private static XcfaLabel handleFmod(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		throw new UnsupportedOperationException("Fmod not yet supported!");
	}

	private static XcfaLabel handleFmin(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 3, "Function is presumed to be binary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpMinExpr.of((Expr<FpType>) callStmt.getParams().get(1), (Expr<FpType>) callStmt.getParams().get(2)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}

	private static XcfaLabel handleFmax(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 3, "Function is presumed to be binary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpMaxExpr.of((Expr<FpType>) callStmt.getParams().get(1), (Expr<FpType>) callStmt.getParams().get(2)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}

	private static XcfaLabel handleFloor(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpRoundToIntegralExpr.of(FpRoundingMode.RTN, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}

	private static XcfaLabel handleFabs(XcfaProcedure.Builder builder, XcfaLabel.ProcedureCallXcfaLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpAbsExpr.of((Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return Stmt(assign);
	}


	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<XcfaLabel> newStmts = new ArrayList<>();
			boolean found = false;
			for (XcfaLabel stmt : edge.getLabels()) {
				if(stmt instanceof XcfaLabel.ProcedureCallXcfaLabel) {
					if(handlers.containsKey(((XcfaLabel.ProcedureCallXcfaLabel) stmt).getProcedure())) {
						newStmts.add(handlers.get(((XcfaLabel.ProcedureCallXcfaLabel) stmt).getProcedure()).apply(builder, (XcfaLabel.ProcedureCallXcfaLabel) stmt));
						found = true;
					}
				}
				else newStmts.add(stmt);
			}
			if(found) {
				builder.removeEdge(edge);
				builder.addEdge(XcfaEdge.of(edge.getSource(), edge.getTarget(), newStmts));
			}
		}
		return builder;
	}

}
