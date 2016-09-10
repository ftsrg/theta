package hu.bme.mit.theta.formalism.common.decl;

import java.util.List;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.theta.formalism.common.type.ProcType;

public interface ProcDecl<ReturnType extends Type> extends Decl<ProcType<ReturnType>, ProcDecl<ReturnType>> {

	@Override
	public ProcRefExpr<ReturnType> getRef();

	public List<? extends ParamDecl<?>> getParamDecls();

	public ReturnType getReturnType();

}
