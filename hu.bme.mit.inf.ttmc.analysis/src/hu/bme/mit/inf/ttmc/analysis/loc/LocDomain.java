package hu.bme.mit.inf.ttmc.analysis.loc;

import hu.bme.mit.inf.ttmc.analysis.Domain;

public class LocDomain implements Domain<LocState> {

	@Override
	public LocState getTop() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public LocState getBottom() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public LocState join(LocState state1, LocState state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public LocState meet(LocState state1, LocState state2) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(LocState state1, LocState state2) {
		return false;
	}


}
