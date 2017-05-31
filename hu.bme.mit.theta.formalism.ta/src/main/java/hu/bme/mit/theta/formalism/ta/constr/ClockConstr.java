package hu.bme.mit.theta.formalism.ta.constr;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface ClockConstr {

	Collection<VarDecl<RatType>> getVars();

	Expr<BoolType> toExpr();

	<P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param);

}
