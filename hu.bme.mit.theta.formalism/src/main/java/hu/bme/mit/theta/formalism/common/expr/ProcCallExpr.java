package hu.bme.mit.theta.formalism.common.expr;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.type.ProcType;

public interface ProcCallExpr<ReturnType extends Type> extends Expr<ReturnType> {
	public Expr<? extends ProcType<? extends ReturnType>> getProc();

	public List<? extends Expr<? extends Type>> getParams();
}
