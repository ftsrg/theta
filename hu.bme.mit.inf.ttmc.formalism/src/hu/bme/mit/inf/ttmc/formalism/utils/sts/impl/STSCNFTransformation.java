package hu.bme.mit.inf.ttmc.formalism.utils.sts.impl;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CNFTransformation;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.STSTransformation;

public final class STSCNFTransformation implements STSTransformation {

	/**
	 * Apply Tseitin transformation to obtain a system where constraints are in
	 * CNF.
	 */
	@Override
	public STS transform(final STS system) {

		final STSImpl.Builder builder = new STSImpl.Builder();
		final CNFTransformation cnfTransf = FormalismUtils.createCNFTransformation();

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

	private Expr<? extends BoolType> transformIfNonCNF(final Expr<? extends BoolType> expr, final CNFTransformation cnfTransf) {
		if (FormalismUtils.isExprCNF(expr))
			return expr;
		else
			return cnfTransf.transform(expr);
	}

}
