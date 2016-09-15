package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.type.ProcType;

public interface ProcRefExpr<ReturnType extends Type> extends RefExpr<ProcType<ReturnType>> {

}
