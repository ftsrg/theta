package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.FuncType;
import hu.bme.mit.inf.theta.core.type.Type;

public interface FuncAppExpr<ParamType extends Type, ResultType extends Type> extends Expr<ResultType> {
	public Expr<? extends FuncType<? super ParamType, ? extends ResultType>> getFunc();
	public Expr<? extends ParamType> getParam();
}
