package hu.bme.mit.inf.ttmc.constraint.ui;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface ConstraintModel {

	public Collection<ConstDecl<? extends Type>> getConstDecls();
	public Collection<Expr<? extends BoolType>> getConstraints();
	
}
