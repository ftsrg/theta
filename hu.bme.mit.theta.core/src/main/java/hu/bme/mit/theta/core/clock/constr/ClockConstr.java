package hu.bme.mit.theta.core.clock.constr;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;

public interface ClockConstr {

	Collection<VarDecl<RatType>> getVars();

	Expr<BoolType> toExpr();

	<P, R> R accept(final ClockConstrVisitor<? super P, ? extends R> visitor, final P param);

}
