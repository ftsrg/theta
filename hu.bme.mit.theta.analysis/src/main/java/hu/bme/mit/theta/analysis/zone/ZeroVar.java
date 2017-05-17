package hu.bme.mit.theta.analysis.zone;

import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.type.impl.Types.Rat;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.RatType;

final class ZeroVar {

	private static final VarDecl<RatType> ZERO_VAR = Var("_zero", Rat());

	private ZeroVar() {
	}

	static VarDecl<RatType> getInstance() {
		return ZERO_VAR;
	}

}
