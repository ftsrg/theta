package hu.bme.mit.inf.theta.formalism.ta.constr;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.ta.utils.ClockConstrVisitor;

public interface ClockConstr {

	public Collection<? extends ClockDecl> getClocks();

	public Expr<? extends BoolType> toExpr();

	public <P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param);

}
