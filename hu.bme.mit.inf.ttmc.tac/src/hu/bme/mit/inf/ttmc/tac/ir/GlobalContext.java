package hu.bme.mit.inf.ttmc.tac.ir;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;

public class GlobalContext {

	private Map<ProcDecl<? extends Type>, Procedure> procedures = new HashMap<>();

	public void addProcedure(Procedure proc) {
		this.procedures.put(proc.getDeclaration(), proc);
	}


}
