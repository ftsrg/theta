package hu.bme.mit.inf.ttmc.formalism.sts;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;

/**
 * Symbolic Transition System (STS) interface.
 * @author Akos
 */
public interface STS {
	/**
	 * Get the collection of variables.
	 * @return Collection of variables
	 */
	public Collection<VarDecl<? extends Type>> getVars();
	
	/**
	 * Get the initial constraints.
	 * @return Initial constraints
	 */
	public Collection<Expr<? extends BoolType>> getInit();
	
	/**
	 * Get the invariant constraints.
	 * @return Invariant constraints
	 */
	public Collection<Expr<? extends BoolType>> getInvar();
	
	/**
	 * Get the transition relation constraints.
	 * @return Transition relation constraints
	 */
	public Collection<Expr<? extends BoolType>> getTrans();
}
