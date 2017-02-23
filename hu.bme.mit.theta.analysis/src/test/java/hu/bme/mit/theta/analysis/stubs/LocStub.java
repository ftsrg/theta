package hu.bme.mit.theta.analysis.stubs;

import java.util.Collection;

import hu.bme.mit.theta.formalism.common.Loc;

public class LocStub implements Loc<LocStub, EdgeStub> {

	@Override
	public Collection<? extends EdgeStub> getInEdges() {
		return null;
	}

	@Override
	public Collection<? extends EdgeStub> getOutEdges() {
		return null;
	}

}
