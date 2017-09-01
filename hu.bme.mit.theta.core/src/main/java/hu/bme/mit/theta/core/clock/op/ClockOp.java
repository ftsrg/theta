package hu.bme.mit.theta.core.clock.op;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.rattype.RatType;

public interface ClockOp {

	Collection<VarDecl<RatType>> getVars();

	Stmt toStmt();

	<P, R> R accept(final ClockOpVisitor<? super P, ? extends R> visitor, final P param);

}
