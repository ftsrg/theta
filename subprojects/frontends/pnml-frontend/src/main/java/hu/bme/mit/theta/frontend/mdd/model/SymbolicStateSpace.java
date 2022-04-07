package hu.bme.mit.theta.frontend.mdd.model;

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddSignature;

import java.util.List;

public interface SymbolicStateSpace {
	MddSignature getMddSetDefinition();
	
	MddHandle getMddRoot();
	
	List<Component> getComponentOrder();
}
