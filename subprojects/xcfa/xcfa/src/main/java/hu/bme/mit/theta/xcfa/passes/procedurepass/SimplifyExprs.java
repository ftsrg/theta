package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.utils.ExprSimplifier;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.ProcedureCall;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class SimplifyExprs extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			XcfaEdge newEdge = edge.mapLabels(label -> {
				if (label instanceof XcfaLabel.StmtXcfaLabel && label.getStmt() instanceof AssignStmt && !(((AssignStmt<?>) label.getStmt()).getVarDecl().getType() instanceof ArrayType)) {
					VarDecl<?> varDecl = ((AssignStmt<?>) label.getStmt()).getVarDecl();
					Expr<?> simplified = ExprSimplifier.simplify(((AssignStmt<?>) label.getStmt()).getExpr(), ImmutableValuation.empty());
					FrontendMetadata.create(simplified, "cType", CComplexType.getType(((AssignStmt<?>) label.getStmt()).getExpr()));
					simplified = ExprSimplifier.simplify(CComplexType.getType(varDecl.getRef()).castTo(simplified), ImmutableValuation.empty());
					FrontendMetadata.create(simplified, "cType", CComplexType.getType(varDecl.getRef()));
					Stmt newStmt = Assign(
							cast(varDecl, varDecl.getType()),
							cast(simplified, varDecl.getType()));
					return Stmt(newStmt);
				} else if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
					List<Expr<?>> newExprs = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams().stream().map((Expr<?> expr) -> {
						final Expr<?> simplified = ExprUtils.simplify(expr);
						FrontendMetadata.create(simplified, "cType", CComplexType.getType(expr));
						return simplified;
					}).collect(Collectors.toList());
					return ProcedureCall(newExprs, ((XcfaLabel.ProcedureCallXcfaLabel) label).getProcedure());
				} else return label;
			});
			if(!edge.getLabels().equals(newEdge.getLabels())) {
				builder.removeEdge(edge);
				builder.addEdge(newEdge);
			}
		}
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}