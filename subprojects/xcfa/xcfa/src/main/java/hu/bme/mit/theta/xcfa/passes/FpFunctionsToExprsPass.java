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

package hu.bme.mit.theta.xcfa.passes;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.fptype.*;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.*;

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

//TODO: type-right conversions (because sqrt and sqrtf might have different domains)
public class FpFunctionsToExprsPass implements ProcedurePass {
	private static final Map<String, BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel>> handlers = new LinkedHashMap<>();

	private static void addHandler(String[] names, BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel> handler) {
		for (String name : names) {
			handlers.put(name, handler);
		}
	}

	static {
		addHandler(new String[]{"fabs", "fabsf", "fabsl"}, FpFunctionsToExprsPass::handleFabs);
		addHandler(new String[]{"floor", "floorf", "floorl"}, FpFunctionsToExprsPass::handleFloor);
		addHandler(new String[]{"fmax", "fmaxf", "fmaxl"}, FpFunctionsToExprsPass::handleFmax);
		addHandler(new String[]{"fmin", "fminf", "fminl"}, FpFunctionsToExprsPass::handleFmin);
		addHandler(new String[]{"fmod", "fmodf", "fmodl"}, FpFunctionsToExprsPass::handleFmod);
		addHandler(new String[]{"sqrt", "sqrtf", "sqrtl"}, FpFunctionsToExprsPass::handleSqrt);
		addHandler(new String[]{"round", "roundf", "roundl"}, FpFunctionsToExprsPass::handleRound);
		addHandler(new String[]{"isnan"}, FpFunctionsToExprsPass::handleIsnan);
		addHandler(new String[]{"trunc"}, FpFunctionsToExprsPass::handleTrunc);
		addHandler(new String[]{"ceil"}, FpFunctionsToExprsPass::handleCeil);
		addHandler(new String[]{"isnormal"}, FpFunctionsToExprsPass::handleIsnormal);
		addHandler(new String[]{"isinf", "__isinf", "__isinff", "__isinfl"}, FpFunctionsToExprsPass::handleIsinf);
		addHandler(new String[]{"isfinite"}, FpFunctionsToExprsPass::handleIsfinite);
		addHandler(new String[]{"__fpclassify", "__fpclassifyf", "__fpclassifyl"}, FpFunctionsToExprsPass::handleFpclassify);
	}

	private static XcfaLabel handleTrunc(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(),
				FpRoundToIntegralExpr.of(FpRoundingMode.RTZ, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleCeil(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(),
				FpRoundToIntegralExpr.of(FpRoundingMode.RTP, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleIsinf(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		CComplexType type = CComplexType.getType(expr);
		//noinspection unchecked
		AssignStmt<?> assign = Assign(
				cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), type.getSmtType()),
				cast(Ite(FpIsInfiniteExpr.of((Expr<FpType>) callStmt.getParams().get(1)), type.getUnitValue(), type.getNullValue()), type.getSmtType()));
		FrontendMetadata.create(assign.getExpr(), "cType", type);
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleIsfinite(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		CComplexType type = CComplexType.getType(expr);
		//noinspection unchecked
		AssignStmt<?> assign = Assign(
				cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), type.getSmtType()),
				cast(Ite(Not(FpIsInfiniteExpr.of((Expr<FpType>) callStmt.getParams().get(1))), type.getUnitValue(), type.getNullValue()), type.getSmtType()));
		FrontendMetadata.create(assign.getExpr(), "cType", type);
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleIsnormal(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		throw new UnsupportedOperationException();
	}


	private static XcfaLabel handleFpclassify(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		throw new UnsupportedOperationException();
	}

	private static XcfaLabel handleIsnan(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		CComplexType type = CComplexType.getType(expr);
		//noinspection unchecked
		AssignStmt<?> assign = Assign(
				cast((VarDecl<?>) ((RefExpr<?>) expr).getDecl(), type.getSmtType()),
				cast(Ite(FpIsNanExpr.of((Expr<FpType>) callStmt.getParams().get(1)), type.getUnitValue(), type.getNullValue()), type.getSmtType()));
		FrontendMetadata.create(assign.getExpr(), "cType", type);
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleRound(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpRoundToIntegralExpr.of(FpRoundingMode.RNA, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleSqrt(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpSqrtExpr.of(FpRoundingMode.RNE, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleFmod(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		throw new UnsupportedOperationException("Fmod not yet supported!");
	}

	private static XcfaLabel handleFmin(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 3, "Function is presumed to be binary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpMinExpr.of((Expr<FpType>) callStmt.getParams().get(1), (Expr<FpType>) callStmt.getParams().get(2)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleFmax(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 3, "Function is presumed to be binary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpMaxExpr.of((Expr<FpType>) callStmt.getParams().get(1), (Expr<FpType>) callStmt.getParams().get(2)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleFloor(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpRoundToIntegralExpr.of(FpRoundingMode.RTN, (Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}

	private static XcfaLabel handleFabs(XcfaProcedureBuilder builder, InvokeLabel callStmt) {
		checkState(callStmt.getParams().size() == 2, "Function is presumed to be unary!");
		Expr<?> expr = callStmt.getParams().get(0);
		checkState(expr instanceof RefExpr);
		//noinspection unchecked
		AssignStmt<FpType> assign = Assign((VarDecl<FpType>) ((RefExpr<?>) expr).getDecl(), FpAbsExpr.of((Expr<FpType>) callStmt.getParams().get(1)));
		FrontendMetadata.create(assign.getExpr(), "cType", CComplexType.getType(expr));
		return new StmtLabel(assign);
	}


	@Override
	public XcfaProcedureBuilder run(XcfaProcedureBuilder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<XcfaLabel> newStmts = new ArrayList<>();
			boolean found = false;
			for (XcfaLabel stmt : ((SequenceLabel)edge.getLabel()).getLabels()) {
				if (stmt instanceof InvokeLabel) {
					if (handlers.containsKey(((InvokeLabel) stmt).getName())) {
						newStmts.add(handlers.get(((InvokeLabel) stmt).getName()).apply(builder, (InvokeLabel) stmt));
						found = true;
					}
				} else newStmts.add(stmt);
			}
			if (found) {
				builder.removeEdge(edge);
				builder.addEdge(new XcfaEdge(edge.getSource(), edge.getTarget(), new SequenceLabel(newStmts)));
			}
		}
		return builder;
	}

}
