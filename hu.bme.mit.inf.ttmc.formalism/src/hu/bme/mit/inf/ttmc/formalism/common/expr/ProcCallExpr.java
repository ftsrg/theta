package hu.bme.mit.inf.ttmc.formalism.common.expr;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

public interface ProcCallExpr<ReturnType extends Type> extends Expr<ReturnType> {
	public Expr<? extends ProcType<? extends ReturnType>> getProc();
	public Collection<? extends Expr<? extends Type>> getParams();
}
