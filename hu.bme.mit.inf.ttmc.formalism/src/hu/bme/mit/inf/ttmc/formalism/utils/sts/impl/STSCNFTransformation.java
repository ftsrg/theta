package hu.bme.mit.inf.ttmc.formalism.utils.sts.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.CNFTransformation;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismExprCNFChecker;
import hu.bme.mit.inf.ttmc.formalism.utils.sts.STSTransformation;

public final class STSCNFTransformation implements STSTransformation {
	private final STSManager manager;
	
	public STSCNFTransformation(STSManager manager) {
		this.manager = manager;
	}
	
	/**
	 * Apply Tseitin transformation to obtain a system where constraints are in CNF.
	 */
	@Override
	public STS transform(STS system) {
		STSImpl.Builder builder = new STSImpl.Builder();
		CNFTransformation cnfTransf = new CNFTransformation(manager, manager.getDeclFactory());
		FormalismExprCNFChecker cnfChecker = new FormalismExprCNFChecker();

		for (Expr<? extends BoolType> expr : system.getInit())
			builder.addInit(transformIfNonCNF(expr, cnfTransf, cnfChecker));
		for (Expr<? extends BoolType> expr : system.getInvar())
			builder.addInvar(transformIfNonCNF(expr, cnfTransf, cnfChecker));
		for (Expr<? extends BoolType> expr : system.getTrans())
			builder.addTrans(transformIfNonCNF(expr, cnfTransf, cnfChecker));

		builder.setProp(transformIfNonCNF(system.getProp(), cnfTransf, cnfChecker));

		return builder.build();
	}
	
	private Expr<? extends BoolType> transformIfNonCNF(Expr<? extends BoolType> expr,
			CNFTransformation cnfTransf, FormalismExprCNFChecker cnfChecker) {
		if (cnfChecker.isExprCNF(expr)) return expr;
		else return cnfTransf.transform(expr);
	}

}
