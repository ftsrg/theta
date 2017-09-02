package hu.bme.mit.theta.core.model;

import java.util.Optional;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Interface for a valuation, which is a mapping from declarations to literal
 * expressions.
 */
public interface Valuation extends Substitution {
	@Override
	<DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl);

	Expr<BoolType> toExpr();
}
