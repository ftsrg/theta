package hu.bme.mit.inf.ttmc.program.tcfa.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.program.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFAEdge;
import hu.bme.mit.inf.ttmc.program.tcfa.TCFALoc;

public final class TCFAImpl implements TCFA {

	private TCFAImpl() {

	}

	////

	public static TCFA copyOf(final TCFA tcfa) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	@Override
	public TCFALoc getInitLoc() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public TCFALoc getFinalLoc() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public TCFALoc getErrorLoc() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends TCFALoc> getLocs() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public Collection<? extends TCFAEdge> getEdges() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
