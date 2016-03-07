package hu.bme.mit.inf.ttmc.constraint.expr;


import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface FuncLitExpr<ParamType extends Type, ResultType extends Type> extends Expr<FuncType<ParamType, ResultType>> {
	
	public ParamDecl<? super ParamType> getParamDecl();
	public Expr<? extends ResultType> getResult();

}
