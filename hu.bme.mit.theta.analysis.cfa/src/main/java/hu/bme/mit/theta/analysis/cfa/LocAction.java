package hu.bme.mit.theta.analysis.cfa;

import hu.bme.mit.theta.analysis.expl.StmtAction;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;

public interface LocAction extends StmtAction {

	CfaEdge getEdge();

}
