package hu.bme.mit.theta.analysis.loc;

import hu.bme.mit.theta.analysis.expl.StmtAction;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;

public interface LocAction extends StmtAction {

	CfaEdge getEdge();

}
