package hu.bme.mit.theta.formalism.sts.utils.impl;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.utils.STSTransformation;

/**
 * Apply Tseitin transformation to obtain an STS where constraints are in CNF.
 * The property is not converted to CNF because of possible negation.
 */
public final class StsCnfTransformation implements STSTransformation {

	@Override
	public STS transform(final STS system) {
		final STS.Builder builder = STS.builder();

		builder.addInit(transformIfNonCNF(system.getInit()));
		builder.addTrans(transformIfNonCNF(system.getTrans()));
		// Should not convert to the property to CNF, because it may be negated
		builder.setProp(system.getProp());

		return builder.build();
	}

	private Expr<BoolType> transformIfNonCNF(final Expr<BoolType> expr) {
		if (ExprUtils.isExprCnf(expr)) return expr;
		else return ExprUtils.transformEquiSatCnf(expr);
	}

}
