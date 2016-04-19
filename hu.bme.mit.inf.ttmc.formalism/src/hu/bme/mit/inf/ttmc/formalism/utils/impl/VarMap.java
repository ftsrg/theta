package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import static com.google.common.base.Preconditions.checkState;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.decl.impl.Decls;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class VarMap {

	private final Map<VarDecl<?>, Map<Integer, ConstDecl<?>>> varToIndexToConst;
	private final Map<ConstDecl<?>, Integer> constToIndex;
	private final Map<ConstDecl<?>, VarDecl<?>> constToVar;

	public VarMap() {
		this.constToIndex = new HashMap<>();
		varToIndexToConst = new HashMap<>();
		constToVar = new HashMap<>();
	}

	public <T extends Type> ConstDecl<T> getConstDecl(final VarDecl<T> varDecl, final int i) {
		Map<Integer, ConstDecl<?>> indexToConst = varToIndexToConst.get(varDecl);
		if (indexToConst == null) {
			indexToConst = new HashMap<>();
			varToIndexToConst.put(varDecl, indexToConst);
		}

		@SuppressWarnings("unchecked")
		ConstDecl<T> constDecl = (ConstDecl<T>) indexToConst.get(i);
		if (constDecl == null) {
			final String name = String.format("_" + varDecl.getName() + "_%d", i);
			constDecl = Decls.Const(name, varDecl.getType());
			indexToConst.put(i, constDecl);
			constToIndex.put(constDecl, i);
			constToVar.put(constDecl, varDecl);
		}

		return constDecl;
	}

	public <T extends Type> VarDecl<T> getVarDecl(final ConstDecl<T> constDecl) {
		@SuppressWarnings("unchecked")
		final VarDecl<T> varDecl = (VarDecl<T>) constToVar.get(constDecl);

		checkState(varDecl != null);
		return varDecl;
	}

	public int getIndex(final ConstDecl<?> constDecl) {
		final Integer index = constToIndex.get(constDecl);

		checkState(index != null);
		return index;
	}

}
