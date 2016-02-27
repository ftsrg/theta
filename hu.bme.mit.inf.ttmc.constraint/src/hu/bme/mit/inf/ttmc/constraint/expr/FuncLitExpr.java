package hu.bme.mit.inf.ttmc.constraint.expr;


import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public interface FuncLitExpr<ParamType extends Type, ResultType extends Type> extends Expr<FuncType<ParamType, ResultType>> {
	
	public ParamDecl<? super ParamType> getParamDecl();
	public Expr<? extends ResultType> getResult();

	@Override
	public default <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
