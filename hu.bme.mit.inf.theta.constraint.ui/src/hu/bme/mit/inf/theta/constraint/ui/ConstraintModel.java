package hu.bme.mit.inf.theta.constraint.ui;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.decl.ConstDecl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.Type;

public interface ConstraintModel {

	public Collection<ConstDecl<? extends Type>> getConstDecls();

	public Collection<Expr<? extends BoolType>> getConstraints();

}
