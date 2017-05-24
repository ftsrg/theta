package hu.bme.mit.theta.core.decl;

import java.util.List;

import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.Type;

public interface ProcDecl<ReturnType extends Type> extends Decl<ProcType<ReturnType>> {

	List<? extends ParamDecl<?>> getParamDecls();

	ReturnType getReturnType();

}
