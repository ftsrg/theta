package hu.bme.mit.inf.theta.formalism.common.expr;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.type.ProcType;

public interface ProcCallExpr<ReturnType extends Type> extends Expr<ReturnType> {
	public Expr<? extends ProcType<? extends ReturnType>> getProc();
	public Collection<? extends Expr<? extends Type>> getParams();
}
