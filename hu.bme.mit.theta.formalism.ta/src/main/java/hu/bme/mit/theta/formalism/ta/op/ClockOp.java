package hu.bme.mit.theta.formalism.ta.op;

import java.util.Collection;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

public interface ClockOp {

	public Collection<? extends ClockDecl> getClocks();

	public Stmt toStmt();

	public <P, R> R accept(final ClockOpVisitor<? super P, ? extends R> visitor, final P param);

}
