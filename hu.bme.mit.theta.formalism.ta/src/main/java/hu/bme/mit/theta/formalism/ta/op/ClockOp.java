package hu.bme.mit.theta.formalism.ta.op;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

public interface ClockOp {

	Collection<VarDecl<RatType>> getClocks();

	Stmt toStmt();

	<P, R> R accept(final ClockOpVisitor<? super P, ? extends R> visitor, final P param);

}
