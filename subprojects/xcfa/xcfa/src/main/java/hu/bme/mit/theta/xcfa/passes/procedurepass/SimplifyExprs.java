package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.utils.ExprSimplifier;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class SimplifyExprs extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<Stmt> newStmts = new ArrayList<>();
			boolean found = false;
			for (Stmt stmt : edge.getLabels()) {
				if (stmt instanceof AssignStmt && !(((AssignStmt<?>) stmt).getVarDecl().getType() instanceof ArrayType)) {
					VarDecl<?> varDecl = ((AssignStmt<?>) stmt).getVarDecl();
					Expr<?> simplified = ExprSimplifier.simplify(((AssignStmt<?>) stmt).getExpr(), ImmutableValuation.empty());
					FrontendMetadata.create(simplified, "cType", CComplexType.getType(((AssignStmt<?>) stmt).getExpr()));
					simplified = ExprSimplifier.simplify(CComplexType.getType(varDecl.getRef()).castTo(simplified), ImmutableValuation.empty());
					FrontendMetadata.create(simplified, "cType", CComplexType.getType(varDecl.getRef()));
					Stmt newStmt = Assign(
							cast(varDecl, varDecl.getType()),
							cast(simplified, varDecl.getType()));
					newStmts.add(newStmt);
					found = true;
				} else if (stmt instanceof XcfaCallStmt) {
					List<Expr<?>> newExprs = ((XcfaCallStmt) stmt).getParams().stream().map(ExprUtils::simplify).collect(Collectors.toList());
					newStmts.add(new XcfaCallStmt(newExprs, ((XcfaCallStmt) stmt).getProcedure()));
					found = true;
				} else newStmts.add(stmt);
			}
			if(found) {
				builder.removeEdge(edge);
				builder.addEdge(XcfaEdge.of(edge.getSource(), edge.getTarget(), newStmts));
			}
		}
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
