package hu.bme.mit.inf.ttmc.core.expr;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface QuantifiedExpr extends UnaryExpr<BoolType, BoolType> {
	
	public List<ParamDecl<? extends Type>> getParamDecls();
}
