package hu.bme.mit.theta.analysis.sts;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;

public class StsAction implements Action {

	final Collection<Expr<? extends BoolType>> trans;

	StsAction(final STS sts) {
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
