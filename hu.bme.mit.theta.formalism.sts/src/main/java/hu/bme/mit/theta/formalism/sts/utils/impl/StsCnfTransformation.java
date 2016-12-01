package hu.bme.mit.theta.formalism.sts.utils.impl;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.CnfTransformation;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.theta.formalism.sts.utils.STSTransformation;

public final class StsCnfTransformation implements STSTransformation {

	/**
	 * Apply Tseitin transformation to obtain a system where constraints are in
	 * CNF.
	 */
	@Override
	public STS transform(final STS system) {

		final StsImpl.Builder builder = new StsImpl.Builder();

		// A new transformation is required for each formula group (init, trans,
		// inv) because they may be added to the solver separately
		CnfTransformation cnfTransf = ExprUtils.createCNFTransformation();
		for (final Expr<? extends BoolType> expr : system.getInit())
			builder.addInit(transformIfNonCNF(expr, cnfTransf));

		cnfTransf = ExprUtils.createCNFTransformation();
		for (final Expr<? extends BoolType> expr : system.getInvar())
			builder.addInvar(transformIfNonCNF(expr, cnfTransf));

		cnfTransf = ExprUtils.createCNFTransformation();
		for (final Expr<? extends BoolType> expr : system.getTrans())
			builder.addTrans(transformIfNonCNF(expr, cnfTransf));

		// Should not convert to the property to CNF, because it may be negated
		builder.setProp(system.getProp());

		return builder.build();
	}

	private Expr<? extends BoolType> transformIfNonCNF(final Expr<? extends BoolType> expr,
			final CnfTransformation cnfTransf) {
		if (ExprUtils.isExprCNF(expr))
			return expr;
		else
			return cnfTransf.transform(expr);
	}

}
