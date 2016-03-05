package hu.bme.mit.inf.ttmc.program.sts;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.decl.VarDecl;

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
	 * Get the initial constarint.
	 * @return Initial constraint
	 */
	public Expr<? extends BoolType> getInit();
	
	/**
	 * Get the invariant constraint
	 * @return Invariant constraint
	 */
	public Expr<? extends BoolType> getInvar();
	
	/**
	 * Get the transition relation constraint.
	 * @return Transition relation constraint
	 */
	public Expr<? extends BoolType> getTrans();
}
