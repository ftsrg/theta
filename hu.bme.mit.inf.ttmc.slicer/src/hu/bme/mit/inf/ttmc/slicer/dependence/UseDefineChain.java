package hu.bme.mit.inf.ttmc.slicer.dependence;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DeclStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.slicer.cfg.BasicBlockCFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;

/*
 * A use-define chain is a list for each use of a variable of all definitions that reach that use.
 */

public class UseDefineChain {

	private class Definition
	{
		public Stmt stmt;
		public StmtCFGNode node;
		public VarDecl<? extends Type> var;

		public Definition(Stmt stmt, StmtCFGNode node, VarDecl<? extends Type> var) {
			this.stmt = stmt;
			this.node = node;
			this.var = var;
		}

		@Override
		public String toString() {
			return this.stmt.toString() + ": " + this.var.toString();
		}
	}

	private class StmtInfo
	{
		public Stmt stmt;

		public Set<VarDecl<? extends Type>> vars = new HashSet<>();
		public Set<Definition> gen = new HashSet<>();
		public Set<Definition> kill = new HashSet<>();
		public Set<Definition> in = new HashSet<>();
		public Set<Definition> out = new HashSet<>();

		public StmtInfo(Stmt stmt) {
			this.stmt = stmt;
		}
	}



}
