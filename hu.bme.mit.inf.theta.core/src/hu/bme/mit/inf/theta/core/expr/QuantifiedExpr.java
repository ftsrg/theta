package hu.bme.mit.inf.theta.core.expr;

import java.util.List;

import hu.bme.mit.inf.theta.core.decl.ParamDecl;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public interface QuantifiedExpr extends UnaryExpr<BoolType, BoolType> {
	
	public List<ParamDecl<? extends Type>> getParamDecls();
}
