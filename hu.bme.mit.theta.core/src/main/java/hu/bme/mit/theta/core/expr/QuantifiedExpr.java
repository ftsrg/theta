package hu.bme.mit.theta.core.expr;

import java.util.List;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public interface QuantifiedExpr extends UnaryExpr<BoolType, BoolType> {

	List<ParamDecl<? extends Type>> getParamDecls();
}
