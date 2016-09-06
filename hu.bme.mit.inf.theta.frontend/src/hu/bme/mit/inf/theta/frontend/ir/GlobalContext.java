package hu.bme.mit.inf.theta.frontend.ir;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.frontend.ir.utils.SymbolTable;

public class GlobalContext {

	private final SymbolTable<Decl<? extends Type, ?>> symbols = new SymbolTable<>();

	private final Map<String, Function> functions = new HashMap<>();
	private Map<String, VarDecl<? extends Type>> globals = new HashMap<>();

	public void addFunction(Function func, ProcDecl<? extends Type> proc) {
		this.functions.put(func.getName(), func);
		this.symbols.put(func.getName(), proc);
	}

	public void addFunctionDeclaration(String name, ProcDecl<? extends Type> proc) {
		this.symbols.put(name, proc);
	}

	public SymbolTable<Decl<? extends Type, ?>> getSymbolTable() {
		return this.symbols;
	}

	public Collection<Function> functions() {
		return Collections.unmodifiableCollection(functions.values());
	}

}
