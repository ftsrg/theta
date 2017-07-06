package hu.bme.mit.theta.core.model;

import java.util.Optional;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;

public interface Valuation extends Substitution {
	@Override
	<DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl);
}
