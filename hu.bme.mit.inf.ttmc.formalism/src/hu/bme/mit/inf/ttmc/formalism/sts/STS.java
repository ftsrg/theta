package hu.bme.mit.inf.ttmc.formalism.sts;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

/**
 * Symbolic Transition System (STS) interface.
 */
public interface STS {
	
	public Collection<VarDecl<? extends Type>> getVars();
	
	public Collection<Expr<? extends BoolType>> getInit();
	
	public Collection<Expr<? extends BoolType>> getInvar();
	
	public Collection<Expr<? extends BoolType>> getTrans();
	
	public Expr<? extends BoolType> getProp();
}
