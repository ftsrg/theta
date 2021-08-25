package hu.bme.mit.theta.xcfa.model;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class XcfaPath {
	private final List<XcfaEdge> edges;

	public XcfaPath(List<XcfaEdge> edges) {
		this.edges = edges;
	}

	public Expr<BoolType> getExpression() {
		Map<VarDecl<?>, ConstDecl<?>> varToLastConstMap = new LinkedHashMap<>();
		Expr<BoolType> ret = True();

		for (XcfaEdge edge : edges) {
			for (Stmt stmt : edge.getStmts()) {
				if (stmt instanceof HavocStmt) {
					VarDecl<?> var = ((HavocStmt<?>) stmt).getVarDecl();
					varToLastConstMap.put(var, Const(var.getName(), var.getType()));
				} else if (stmt instanceof AssumeStmt) {
					Expr<BoolType> expr = XcfaStmtVarReplacer.replaceVars(((AssumeStmt) stmt).getCond(), varToLastConstMap);
					ret = And(ret, expr);
				} else if (stmt instanceof AssignStmt) {
					VarDecl<?> var = ((AssignStmt<?>) stmt).getVarDecl();
					ConstDecl<?> cnst = Const(var.getName(), var.getType());
					Expr<?> expr = XcfaStmtVarReplacer.replaceVars(((AssignStmt<?>) stmt).getExpr(), varToLastConstMap);
					ret = And(ret, Eq(cnst.getRef(), expr));
					varToLastConstMap.put(var, cnst);
				} else throw new UnsupportedOperationException("Not yet implemented!");
			}
		}
		return ret;
	}
}
