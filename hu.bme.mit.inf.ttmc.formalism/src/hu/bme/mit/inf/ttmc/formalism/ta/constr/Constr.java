package hu.bme.mit.inf.ttmc.formalism.ta.constr;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ConstrVisitor;

public interface Constr {

	public Expr<? extends BoolType> asExpr();

	public <P, R> R accept(final ConstrVisitor<? super P, ? extends R> visitor, final P param);

}
