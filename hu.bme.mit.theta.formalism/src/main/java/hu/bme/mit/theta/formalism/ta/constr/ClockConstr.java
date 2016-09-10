package hu.bme.mit.theta.formalism.ta.constr;

import java.util.Collection;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.utils.ClockConstrVisitor;

public interface ClockConstr {

	public Collection<? extends ClockDecl> getClocks();

	public Expr<? extends BoolType> toExpr();

	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param);

}
