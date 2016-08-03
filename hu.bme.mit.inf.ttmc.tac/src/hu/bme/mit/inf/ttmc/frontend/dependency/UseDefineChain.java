package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;
import hu.bme.mit.inf.ttmc.frontend.ir.node.AssignNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.IrNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.JumpIfNode;
import hu.bme.mit.inf.ttmc.frontend.ir.node.NonTerminatorIrNode;

public class UseDefineChain {

	private static class Definition {
		public VarDecl<? extends Type> var;
		public BasicBlock block;
		public NonTerminatorIrNode node;

		public Definition(VarDecl<? extends Type> var, BasicBlock block, NonTerminatorIrNode node) {
			this.var = var;
			this.block = block;
			this.node = node;
		}

		@Override
		public String toString() {
			return this.node.getLabel();
		}
	}

	private static class Use {
		public Set<VarDecl<? extends Type>> vars;
		public BasicBlock block;
		public NonTerminatorIrNode node;

		public Use(BasicBlock block, NonTerminatorIrNode node, Set<VarDecl<? extends Type>> vars) {
			this.block = block;
			this.node = node;
			this.vars = vars;
		}
	}

	private static class BlockInfo {
		public BasicBlock block;

		public Set<Definition> gen = new HashSet<>();
		public Set<Definition> kill = new HashSet<>();
		public Set<Definition> in = new HashSet<>();
		public Set<Definition> out = new HashSet<>();

		public Set<VarDecl<? extends Type>> defs = new HashSet<>();
		public Set<Use> uses = new HashSet<>();

		public BlockInfo(BasicBlock block) {
			this.block = block;
		}
	}

	private final Map<BasicBlock, BlockInfo> blocks;

	private UseDefineChain(Map<BasicBlock, BlockInfo> blocks) {
		this.blocks = blocks;
	}

	public static UseDefineChain buildChain(Function function) {
		VariableFinderVisitor varFinder = new VariableFinderVisitor();
		Map<BasicBlock, BlockInfo> blocks = new HashMap<>();
		List<Definition> allDefs = new ArrayList<>();

		/* Find all uses and definitions for each block */
		for (BasicBlock block : function.getBlocks()) {
			BlockInfo info = new BlockInfo(block);

			List<Definition> defs = new ArrayList<>();

			for (NonTerminatorIrNode node : block.getNodes()) {
				Set<VarDecl<? extends Type>> usedVars = new HashSet<>();
				if (node instanceof AssignNode<?, ?>) {
					AssignNode<? extends Type, ? extends Type> assign = (AssignNode<? extends Type, ? extends Type>) node;

					// Add this assignment to definitions
					Definition def = new Definition(assign.getVar(), block, node);

					defs.add(def);
					info.gen.add(def);

					// Find all uses
					assign.getExpr().accept(varFinder, usedVars);
					Use use = new Use(block, node, usedVars);
					info.uses.add(use);

				} else if (node instanceof JumpIfNode) {
					((JumpIfNode) node).getCond().accept(varFinder, usedVars);
					Use use = new Use(block, node, usedVars);
					info.uses.add(use);
				}
			}

			allDefs.addAll(defs);
			blocks.put(block, info);
		}

		/* Compute kill sets */
		for (BlockInfo info : blocks.values()) {
			List<VarDecl<? extends Type>> vars = info.gen.stream().map(d -> d.var).collect(Collectors.toList());
			List<Definition> defs = allDefs.stream().filter(d -> vars.contains(d.var)).collect(Collectors.toList());

			info.kill.addAll(defs);
			info.kill.removeAll(info.gen);
		}


		/*
		 * Iterative solution for reaching definitions.
		 * (Compilers: Principles, Techniques and Tools, 1st edition, Algorithm 10.2)
		 */
		for (BlockInfo blockInfo : blocks.values()) {
			blockInfo.out.addAll(blockInfo.gen);
		}

		boolean change = true;
		while (change) {
			change = false;
			for (BlockInfo blockInfo : blocks.values()) {
				/* in[B] = for all p in parent(B) Union {out[p]} */
				Set<Definition> newIn = new HashSet<>();
				blockInfo.block.parents().forEach(s -> {
					newIn.addAll(blocks.get(s).out);
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

		return new UseDefineChain(blocks);
	}

}
