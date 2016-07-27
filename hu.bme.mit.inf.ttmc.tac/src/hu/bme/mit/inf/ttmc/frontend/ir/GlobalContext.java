package hu.bme.mit.inf.ttmc.frontend.ir;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class GlobalContext {

	private Map<String, Function> functions = new HashMap<>();
	private Map<String, VarDecl<? extends Type>> globals = new HashMap<>();

	public void addFunction(Function func) {
		this.functions.put(func.getName(), func);
	}

}
