package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.List;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CCall extends CStatement{
	private final VarDecl<?> ret;
	private final String functionId;
	private final List<CStatement> params;

	public CCall(String functionId, List<CStatement> params) {
		this.functionId = functionId;
		this.params = params;
		ret = Var("functionret", Int());
	}

	public String getFunctionId() {
		return functionId;
	}

	public List<CStatement> getParams() {
		return params;
	}

	public VarDecl<?> getRet() {
		return ret;
	}
}
