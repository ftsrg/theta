package hu.bme.mit.inf.theta.frontend.ir;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.frontend.ir.utils.SymbolTable;

public class GlobalContext {

	private class GlobalVariable<T extends Type> {
		private final VarDecl<T> decl;
		private final Expr<? extends T> init;

		public GlobalVariable(VarDecl<T> decl, Expr<? extends T> init) {
			this.decl = decl;
			this.init = init;
		}
	}

	private final SymbolTable<Decl<? extends Type, ?>> symbols = new SymbolTable<>();

	private final Map<String, Function> functions = new HashMap<>();
	private Set<GlobalVariable<?>> globals = new HashSet<>();

	public void addFunction(Function func, ProcDecl<? extends Type> proc) {
		func.setContext(this);
		this.functions.put(func.getName(), func);
		this.symbols.put(func.getName(), proc);
	}

	public void addFunctionDeclaration(String name, ProcDecl<? extends Type> proc) {
		this.symbols.put(name, proc);
	}

	public SymbolTable<Decl<? extends Type, ?>> getSymbolTable() {
		return this.symbols;
	}

	public Function getFunctionByName(String name) {
		return this.functions.get(name);
	}

	public Collection<Function> functions() {
		return Collections.unmodifiableCollection(functions.values());
	}

	public <T extends Type, E extends T> void addGlobal(String name, VarDecl<T> var, Expr<E> init) {
		this.symbols.putGlobal(name, var);
		this.globals.add(new GlobalVariable<>(var, init));
	}

	public Collection<VarDecl<? extends Type>> globals() {
		return this.globals.stream().map(glob -> glob.decl).collect(Collectors.toList());
	}

}
