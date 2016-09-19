package hu.bme.mit.theta.core.decl;

import java.util.List;

import hu.bme.mit.theta.core.expr.ProcRefExpr;
import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.Type;

public interface ProcDecl<ReturnType extends Type> extends Decl<ProcType<ReturnType>> {

	@Override
	public ProcRefExpr<ReturnType> getRef();

	public List<? extends ParamDecl<?>> getParamDecls();

	public ReturnType getReturnType();

}
