package hu.bme.mit.inf.ttmc.constraint.expr;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface QuantifiedExpr extends UnaryExpr<BoolType, BoolType> {
	
	public List<ParamDecl<? extends Type>> getParamDecls();
}
