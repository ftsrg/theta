package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import java.util.HashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class VarMap {
	
	private final DeclFactory factory;
	
	private final Map<VarDecl<?>, Map<Integer, ConstDecl<?>>> varToIndexToConst;
	private final Map<ConstDecl<?>, Integer> constToIndex;
	private final Map<ConstDecl<?>, VarDecl<?>> constToVar;
	
	public VarMap(DeclFactory factory) {
		this.factory = factory;
		this.constToIndex = new HashMap<>();
		varToIndexToConst = new HashMap<>();
		constToVar = new HashMap<>();
	}
	
	public <T extends Type> ConstDecl<T> getConstDecl(VarDecl<T> varDecl, int i) {
		Map<Integer, ConstDecl<?>> indexToConst = varToIndexToConst.get(varDecl);
		if (indexToConst == null) {
			indexToConst = new HashMap<>();
			varToIndexToConst.put(varDecl, indexToConst);
		}
		
		@SuppressWarnings("unchecked")
		ConstDecl<T> constDecl = (ConstDecl<T>) indexToConst.get(i);
		if (constDecl == null) {
			final String name = String.format("_" + varDecl.getName() + "_%d", i);
			constDecl = factory.Const(name, varDecl.getType());
			indexToConst.put(i, constDecl);
			constToIndex.put(constDecl, i);
			constToVar.put(constDecl, varDecl);
		}
			
		return constDecl;
	}
	
	public <T extends Type> VarDecl<T> getVarDecl(ConstDecl<T> constDecl) {
		@SuppressWarnings("unchecked")
		final VarDecl<T> varDecl = (VarDecl<T>) constToVar.get(constDecl);
		
		checkState(varDecl != null);
		return varDecl;
	}
	
	public int getIndex(ConstDecl<?> constDecl) {
		final Integer index = constToIndex.get(constDecl);
		
		checkState(index != null);
		return index;
	}

}
