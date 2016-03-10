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
		// Keep variables
		builder.addVar(system.getVars());
		// Transform initial constraints
		for (Expr<? extends BoolType> expr : system.getInit()) {
			if (cnfChecker.isExprCNF(expr)) builder.addInit(expr);
			else builder.addInit(cnfTransf.transform(expr));
		}
		// Transform invariant constraints
		for (Expr<? extends BoolType> expr : system.getInvar()) {
			if (cnfChecker.isExprCNF(expr)) builder.addInvar(expr);
			else builder.addInvar(cnfTransf.transform(expr));
		}
		// Transform transition constraints
		for (Expr<? extends BoolType> expr : system.getTrans()) {
			if (cnfChecker.isExprCNF(expr)) builder.addTrans(expr);
			else builder.addTrans(cnfTransf.transform(expr));
		}
		// Transform the property
		if (cnfChecker.isExprCNF(system.getProp())) builder.setProp(system.getProp());
		else builder.setProp(cnfTransf.transform(system.getProp()));
		// Add new variables
		builder.addVar(cnfTransf.getRepresentatives());

		return builder.build();
	}

}
