package hu.bme.mit.inf.ttmc.analysis.sts;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

public class STSAction implements Action {

	final Collection<Expr<? extends BoolType>> trans;

	STSAction(final STS sts) {
		this.trans = sts.getTrans();
	}

	public Collection<Expr<? extends BoolType>> getTrans() {
		return trans;
	}

	@Override
	public String toString() {
		return trans.toString();
	}
}
