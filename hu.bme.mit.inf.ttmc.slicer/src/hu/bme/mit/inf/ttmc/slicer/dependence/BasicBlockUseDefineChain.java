package hu.bme.mit.inf.ttmc.slicer.dependence;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
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

/*
 * A use-define chain is a list for each use of a variable of all definitions that reach that use.
 */

public class BasicBlockUseDefineChain {

	private static class Definition
	{
		private static int cnt = 0;

		public int id;
		public Stmt stmt;
		public BasicBlockCFGNode block;
		public VarDecl<? extends Type> var;

		public Definition(Stmt stmt, BasicBlockCFGNode block, VarDecl<? extends Type> var) {
			this.id = ++cnt;
			this.stmt = stmt;
			this.block = block;
			this.var = var;
		}

		@Override
		public String toString() {
			return this.stmt.toString() + ": " + this.var.toString();
		}
	}

	private static class BlockInfo
	{
		public BasicBlockCFGNode block;
		public Set<VarDecl<? extends Type>> vars = new HashSet<>();
		public Set<Definition> gen = new HashSet<>();
		public Set<Definition> kill = new HashSet<>();
		public Set<Definition> in = new HashSet<>();
		public Set<Definition> out = new HashSet<>();

		public BlockInfo(BasicBlockCFGNode block) {
			this.block = block;
		}
	}

	private Map<BasicBlockCFGNode, BlockInfo> blocks = new HashMap<>();
	//private Map<Use, Set<Definition>> udInfo = new HashMap<>();
	private Set<Definition> definitions = new HashSet<>();

	private CFG cfg;
	private List<CFGNode> nodes;

	public BasicBlockUseDefineChain(CFG cfg) {
		this.cfg = cfg;
		this.nodes = cfg.nodes();
		this.analyzeBlocks();
	}

	private void analyzeBlocks() {
		this.findAllDefinitions();

		// Compute kill sets for basic blocks
		for (BlockInfo blockInfo : this.blocks.values()) {
			// Kill contains all other definitions of the variables defined in this block
			blockInfo.kill.addAll(this.definitions.stream().filter(s -> blockInfo.vars.contains(s.var)).collect(Collectors.toSet()));
			blockInfo.kill.removeAll(blockInfo.gen);
			System.out.println("Block: " +  blockInfo.block + "\n    Gen: " + blockInfo.gen + "\n    Kill: " + blockInfo.kill);
		}

		/*
		 * Iterative algorithm for reaching definitions.
		 * (Compilers: Principles, Techniques and Tools, 1st edition, Algorithm 10.2)
		 */
		for (BlockInfo blockInfo : this.blocks.values()) {
			blockInfo.out.addAll(blockInfo.gen);
		}

		boolean change = true;
		while (change) {
			change = false;
			for (BlockInfo blockInfo : this.blocks.values()) {
				/* in[B] = for all p in parent(B) Union {out[p]} */
				Set<Definition> newIn = new HashSet<>();
				blockInfo.block.getBlockParents().forEach(s -> {
					newIn.addAll(this.blocks.get(s).out);
				});
				blockInfo.in = newIn;

				/* out[B] = gen[B] union (in[B] sub kill[B]) */
				Set<Definition> newOut = new HashSet<>(blockInfo.gen);
				newOut.addAll(blockInfo.in.stream().filter(s -> !blockInfo.kill.contains(s)).collect(Collectors.toSet()));

				if (!blockInfo.out.equals(newOut)) {
					blockInfo.out = newOut;
					change = true;
				}
			}
		}

		for (BlockInfo blockInfo : this.blocks.values()) {
			System.out.println("Block: "
				+  blockInfo.block +
				"\n    Gen: " + blockInfo.gen +
				"\n    Kill: " + blockInfo.gen +
				"\n    In: " + blockInfo.in +
				"\n    Out: " + blockInfo.out
			);
		}
	}

	private void findAllDefinitions() {
		for (CFGNode node : this.nodes) {
			if (node instanceof BasicBlockCFGNode) {
				BasicBlockCFGNode bb = (BasicBlockCFGNode) node;
				BlockInfo blockInfo = new BlockInfo(bb);

				for (Stmt stmt : bb.getStmts()) {
					Set<VarDecl<? extends Type>> defs = VariableFinderVisitor.findLeftVars(stmt);
					Set<VarDecl<? extends Type>> uses = VariableFinderVisitor.findRightVars(stmt);

					for (VarDecl<? extends Type> var : defs) {
						Definition defInfo = new Definition(stmt, bb, var);
						this.definitions.add(defInfo);
						blockInfo.gen.add(defInfo);
						blockInfo.vars.add(var);
					}

					for (VarDecl<? extends Type> var : uses) {
						//Definition useInfo = new Definition(stmt, bb, var);
					}
				}
				this.blocks.put(bb, blockInfo);
			}
		}
	}


}
