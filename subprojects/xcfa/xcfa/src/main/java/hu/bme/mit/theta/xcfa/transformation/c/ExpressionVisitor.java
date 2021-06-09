package hu.bme.mit.theta.xcfa.transformation.c;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.dsl.gen.CBaseVisitor;
import hu.bme.mit.theta.xcfa.transformation.c.statements.CStatement;

import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;

public abstract class AbstractExpressionVisitor extends CBaseVisitor<Expr<?>> {
	protected final List<CStatement> preStatements = new ArrayList<>();
	protected final List<CStatement> postStatements = new ArrayList<>();
	protected final Deque<Map<String, VarDecl<?>>> variables;
	private static boolean isBitwiseOps = false;

	public List<CStatement> getPostStatements() {
		return postStatements;
	}

	public List<CStatement> getPreStatements() {
		return preStatements;
	}
}
