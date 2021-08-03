package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.ExprSimplifier;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;

import java.util.ArrayList;
import java.util.List;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class SimplifyExprs extends ProcedurePass{
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<Stmt> newStmts = new ArrayList<>();
			boolean found = false;
			for (Stmt stmt : edge.getStmts()) {
				if(stmt instanceof AssignStmt) {
					VarDecl<?> varDecl = ((AssignStmt<?>) stmt).getVarDecl();
					Expr<?> simplified = ExprSimplifier.simplify(((AssignStmt<?>) stmt).getExpr(), ImmutableValuation.empty());
					XcfaMetadata.create(simplified, "cType", CComplexType.getType(((AssignStmt<?>) stmt).getExpr()));
					Stmt newStmt = Assign(
							cast(varDecl, varDecl.getType()),
							cast(CComplexType.getType(varDecl.getRef()).castTo(simplified), varDecl.getType()));
					newStmts.add(newStmt);
					found = true;
				}
				else newStmts.add(stmt);
			}
			if(found) {
				builder.removeEdge(edge);
				builder.addEdge(new XcfaEdge(edge.getSource(), edge.getTarget(), newStmts));
			}
		}
		return builder;
	}
}
