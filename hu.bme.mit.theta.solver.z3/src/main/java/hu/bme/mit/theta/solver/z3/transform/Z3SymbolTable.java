package hu.bme.mit.theta.solver.z3.transform;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.Maps;

import hu.bme.mit.theta.core.decl.ConstDecl;

public class Z3SymbolTable {

	private final BiMap<ConstDecl<?>, com.microsoft.z3.FuncDecl> constToSymbol;

	public Z3SymbolTable() {
		constToSymbol = Maps.synchronizedBiMap(HashBiMap.create());
	}

	public boolean definesConst(final ConstDecl<?> constDecl) {
		return constToSymbol.containsKey(constDecl);
	}

	public boolean definesSymbol(final com.microsoft.z3.FuncDecl symbol) {
		return constToSymbol.inverse().containsKey(symbol);
	}

	public com.microsoft.z3.FuncDecl getSymbol(final ConstDecl<?> constDecl) {
		checkArgument(definesConst(constDecl));
		return constToSymbol.get(constDecl);
	}

	public ConstDecl<?> getConst(final com.microsoft.z3.FuncDecl symbol) {
		checkArgument(definesSymbol(symbol));
		return constToSymbol.inverse().get(symbol);
	}

	public void put(final ConstDecl<?> constDecl, final com.microsoft.z3.FuncDecl symbol) {
		checkNotNull(constDecl);
		checkNotNull(symbol);
		checkState(!constToSymbol.containsKey(constDecl));
		constToSymbol.put(constDecl, symbol);
	}

}
