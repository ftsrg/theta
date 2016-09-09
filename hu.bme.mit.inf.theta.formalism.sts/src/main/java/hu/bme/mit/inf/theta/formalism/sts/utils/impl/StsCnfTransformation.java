package hu.bme.mit.inf.theta.formalism.sts.utils.impl;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.sts.STS;
import hu.bme.mit.inf.theta.formalism.sts.impl.StsImpl;
import hu.bme.mit.inf.theta.formalism.sts.utils.STSTransformation;
import hu.bme.mit.inf.theta.formalism.utils.FormalismUtils;
import hu.bme.mit.inf.theta.formalism.utils.impl.CnfTransformation;

public final class StsCnfTransformation implements STSTransformation {

	/**
	 * Apply Tseitin transformation to obtain a system where constraints are in
	 * CNF.
	 */
	@Override
	public STS transform(final STS system) {

		final StsImpl.Builder builder = new StsImpl.Builder();
		final CnfTransformation cnfTransf = FormalismUtils.createCNFTransformation();

		for (final Expr<? extends BoolType> expr : system.getInit())
			builder.addInit(transformIfNonCNF(expr, cnfTransf));
		cnfTransf.clearRepresentatives();

		for (final Expr<? extends BoolType> expr : system.getInvar())
			builder.addInvar(transformIfNonCNF(expr, cnfTransf));
		cnfTransf.clearRepresentatives();

		for (final Expr<? extends BoolType> expr : system.getTrans())
			builder.addTrans(transformIfNonCNF(expr, cnfTransf));
		cnfTransf.clearRepresentatives();

		builder.setProp(system.getProp());

		return builder.build();
	}

	private Expr<? extends BoolType> transformIfNonCNF(final Expr<? extends BoolType> expr,
			final CnfTransformation cnfTransf) {
		if (FormalismUtils.isExprCNF(expr))
			return expr;
		else
			return cnfTransf.transform(expr);
	}

}
