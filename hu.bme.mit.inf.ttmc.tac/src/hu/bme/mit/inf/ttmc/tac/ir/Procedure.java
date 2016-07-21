package hu.bme.mit.inf.ttmc.tac.ir;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public class Procedure {

	private ProcDecl<? extends Type> procDecl;
	private List<TACNode> instructions;
	private List<VarDecl<? extends Type>> locals = new ArrayList<>();

	public Procedure(ProcDecl<? extends Type> procDecl) {
		this.procDecl = procDecl;
	}

	public ProcDecl<? extends Type> getDeclaration() {
		return this.procDecl;
	}

	public void append(TACNode instr) {
		this.instructions.add(instr);
	}

}
