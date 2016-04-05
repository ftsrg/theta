package hu.bme.mit.inf.ttmc.constraint.z3.trasform;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;

import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;

class Z3SymbolTable {

	private final BiMap<ConstDecl<?>, com.microsoft.z3.FuncDecl> constToSymbol;

	Z3SymbolTable() {
		constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
	}

	public com.microsoft.z3.FuncDecl getSymbol(final ConstDecl<?> constDecl) {
		return constToSymbol.get(constDecl);
	}

	public ConstDecl<?> getConst(final com.microsoft.z3.FuncDecl symbol) {
		return constToSymbol.inverse().get(symbol);
	}

	public void put(final ConstDecl<?> constDecl, final com.microsoft.z3.FuncDecl symbol) {
		checkNotNull(constDecl);
		checkNotNull(symbol);
		checkState(!constToSymbol.containsKey(constDecl));
		constToSymbol.put(constDecl, symbol);
	}

}
