package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.decl.ProcDecl;
import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.Type;

public abstract class ProcRefExpr<ReturnType extends Type> extends RefExpr<ProcType<ReturnType>> {

	@Override
	public abstract ProcDecl<ReturnType> getDecl();

}
