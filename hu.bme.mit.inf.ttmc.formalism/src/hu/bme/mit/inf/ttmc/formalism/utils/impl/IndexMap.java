package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;

public class IndexMap {
	
	private final Map<VarDecl<?>, Integer> varToIndex;
	
	public IndexMap() {
		varToIndex = new HashMap<>();
	}
	
	public int getIndex(VarDecl<?> varDecl) {
		Integer index = varToIndex.get(varDecl);
		if (index == null) {
			index = 0;
			varToIndex.put(varDecl, 0);
		}
		
		return index;
	}

	public void inc(final VarDecl<?> varDecl) {
		final int index = getIndex(varDecl);
		varToIndex.put(varDecl, index + 1);
	}

}
