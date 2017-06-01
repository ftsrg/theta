package hu.bme.mit.theta.formalism.sts.utils.impl;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.CnfTransformation;
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
		// A new transformation is required for each formula group (init, trans)
		// because they may be added to the solver separately
		CnfTransformation cnfTransf = ExprUtils.createCNFTransformation();
		builder.addInit(transformIfNonCNF(system.getInit(), cnfTransf));

		cnfTransf = ExprUtils.createCNFTransformation();
		builder.addTrans(transformIfNonCNF(system.getTrans(), cnfTransf));

		// Should not convert to the property to CNF, because it may be negated
		builder.setProp(system.getProp());

		return builder.build();
	}

	private Expr<BoolType> transformIfNonCNF(final Expr<BoolType> expr,
			final CnfTransformation cnfTransf) {
		if (ExprUtils.isExprCnf(expr))
			return expr;
		else
			return cnfTransf.transform(expr);
	}

}
