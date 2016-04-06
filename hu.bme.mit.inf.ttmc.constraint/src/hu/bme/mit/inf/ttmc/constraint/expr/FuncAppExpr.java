package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface FuncAppExpr<ParamType extends Type, ResultType extends Type> extends Expr<ResultType> {
	public Expr<? extends FuncType<? super ParamType, ? extends ResultType>> getFunc();
	public Expr<? extends ParamType> getParam();
}
