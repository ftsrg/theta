package hu.bme.mit.theta.analysis.zone;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

final class ZeroVar {

	private static final VarDecl<RatType> ZERO_VAR = Var("_zero", Rat());

	private ZeroVar() {
	}

	static VarDecl<RatType> getInstance() {
		return ZERO_VAR;
	}

}
