package hu.bme.mit.inf.ttmc.tac.ir;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class Assign {

	private VarDecl<? extends Type> var;
	private Expr<? extends Type> expr;

	public VarDecl<? extends Type> getVarDecl() {
		return this.var;
	}

	public Expr<? extends Type> getExpr() {
		return this.expr;
	}
}
