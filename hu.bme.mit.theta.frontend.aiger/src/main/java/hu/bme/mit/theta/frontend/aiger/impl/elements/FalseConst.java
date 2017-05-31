package hu.bme.mit.theta.frontend.aiger.impl.elements;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class FalseConst extends HwElement {

	public FalseConst() {
		super(0);
	}

	@Override
	public Expr<? extends BoolType> getExpr(final List<HwElement> elements) {
		return False();
	}

}
