package hu.bme.mit.theta.frontend.c.dependency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.AssertNode;
import hu.bme.mit.theta.frontend.c.ir.node.AssignNode;
import hu.bme.mit.theta.frontend.c.ir.node.ConditionalTerminatorNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.ir.node.NonTerminatorIrNode;

/**
 * Data-flow information
 *
 * @author Gyula Sallai <salla@sch.bme.hu>
 */
public class UseDefineChain {

	/**
	 * An internal class for storing definition information
	 */
	public static class Definition {
		public VarDecl<? extends Type> var;
		public NonTerminatorIrNode node;

		public Definition(final VarDecl<? extends Type> var, final NonTerminatorIrNode node) {
			this.var = var;
			this.node = node;
		}

		@Override
		public String toString() {
			return this.node.getLabel();
		}
	}

	/**
	 * An internal class for storing use information
	 */
	private static class Use {
		public VarDecl<? extends Type> var;
		public IrNode node;

		public Use(final IrNode node, final VarDecl<? extends Type> var) {
			this.node = node;
			this.var = var;
		}

		@Override
		public String toString() {
			return "(" + this.node.getLabel() + ": " + this.var.toString() + ")";
		}
	}

	/**
	 * An internal class for storing basic block data flow information
	 */
	private static class BlockInfo {
		public BasicBlock block;

		public Set<Definition> gen = new HashSet<>();
		public Set<Definition> kill = new HashSet<>();
		public Set<Definition> in = new HashSet<>();
		public Set<Definition> out = new HashSet<>();

		public Set<Use> use = new HashSet<>();
		public Set<Use> def = new HashSet<>();
		public Set<Use> uIn = new HashSet<>();
		public Set<Use> uOut = new HashSet<>();

		public Map<IrNode, List<Use>> uses = new HashMap<>();
		public Map<IrNode, Definition> defs = new HashMap<>();

		public BlockInfo(final BasicBlock block) {
			this.block = block;
		}
	}

	private final Map<BasicBlock, BlockInfo> blocks;

	private UseDefineChain(final Map<BasicBlock, BlockInfo> blocks) {
		this.blocks = blocks;
	}

	/**
	 * Returns all definitions generated inside a given block
	 *
	 * @param block
	 *            A BasicBlock
	 *
	 * @return A set of definitions created in block
	 */
	public Set<Definition> getGeneratedDefinitions(final BasicBlock block) {
		final BlockInfo info = this.blocks.get(block);
		if (info == null)
			throw new RuntimeException("Cannot find block '" + block.getName() + "' in the use-define chain.");

		return Collections.unmodifiableSet(info.gen);
	}

	/**
	 * Returns all definitions which reach an instruction node
	 *
	 * @param node
	 *            An instruction node
	 *
	 * @return A collection of assignment instructions whose values reach node
	 */
	public List<NonTerminatorIrNode> getDefinitions(final IrNode node) {
		final BasicBlock block = node.getParentBlock();
		final BlockInfo info = this.blocks.get(block);

		if (info == null)
			throw new RuntimeException("Cannot find block '" + block.getName() + "' (containing instruction "
					+ node.getLabel() + ") in the use-define chain.");

		final List<Use> uses = info.uses.get(node);
		if (uses == null)
			return Collections.emptyList();

		final List<VarDecl<? extends Type>> usedVars = info.uses.get(node).stream().map(u -> u.var)
				.collect(Collectors.toList());

		return this.getLocalReachingDefinitions(node).stream().filter(d -> usedVars.contains(d.var)).map(d -> d.node)
				.collect(Collectors.toList());
	}

	/**
	 * Returns the definitions reaching the beginning of a given block
	 *
	 * @param block
	 *            A BasicBlock
	 *
	 * @return A set of definitions reaching block
	 */
	public Set<Definition> getReachingDefinitions(final BasicBlock block) {
		final BlockInfo info = this.blocks.get(block);
		if (info == null)
			throw new RuntimeException("Cannot find block '" + block.getName() + "' in the use-define chain.");

		return Collections.unmodifiableSet(info.in);
	}

	/**
	 * Returns the local reaching definitions for an instruction
	 *
	 * @param node
	 *            An instruction node
	 *
	 * @return A set of definitions reaching an instruction
	 */
	public Set<Definition> getLocalReachingDefinitions(final IrNode node) {
		final BasicBlock block = node.getParentBlock();
		final BlockInfo info = this.blocks.get(block);

		if (info == null)
			throw new RuntimeException("Cannot find block '" + block.getName() + "' in the use-define chain.");

		if (node == block.getTerminator()) {
			// A terminator's local reaching definitions is the same as the
			// block's out definitions
			return new HashSet<>(info.out);
		}

		final Set<Definition> defs = new HashSet<>(info.in);
		final List<NonTerminatorIrNode> nodes = block.getNodes();

		final int idx = nodes.indexOf(node);
		for (int i = 0; i < idx; i++) {
			final IrNode instr = nodes.get(i);
			if (instr instanceof AssignNode<?, ?>) {
				final AssignNode<?, ?> assign = (AssignNode<?, ?>) instr;
				defs.removeIf(d -> d.var == assign.getVar());
				defs.add(new Definition(assign.getVar(), assign));
			}
		}

		return defs;
	}

	/**
	 * Return all reachable uses of an assignment node
	 *
	 * @param node
	 *            An assignment node
	 *
	 * @return A collection of instruction nodes
	 */
	public Collection<IrNode> getUses(final AssignNode<?, ?> node) {
		final BasicBlock block = node.getParentBlock();
		final BlockInfo info = this.blocks.get(block);

		if (info == null)
			throw new RuntimeException("Cannot find block '" + block.getName() + "' in the use-define chain.");

		final VarDecl<? extends Type> definedVar = info.defs.get(node).var;

		return this.getLocalReachableUses(node).stream().filter(u -> u.var == definedVar).map(u -> u.node)
				.collect(Collectors.toList());
	}

	/**
	 * Returns the uses reaching the end of a given block
	 *
	 * @param block
	 *            A BasicBlock
	 *
	 * @return A set of uses reaching block
	 */
	public Set<Use> getReachableUses(final BasicBlock block) {
		final BlockInfo info = this.blocks.get(block);
		if (info == null)
			throw new RuntimeException("Cannot find block '" + block.getName() + "' in the use-define chain.");

		return Collections.unmodifiableSet(info.uOut);
	}

	/**
	 * Returns a set of uses reached by an assignment
	 *
	 * @param node
	 *
	 * @return
	 */
	public Set<Use> getLocalReachableUses(final NonTerminatorIrNode node) {
		final BasicBlock block = node.getParentBlock();
		final BlockInfo info = this.blocks.get(block);

		if (info == null)
			throw new RuntimeException("Cannot find block '" + block.getName() + "' in the use-define chain.");

		final Set<Use> uses = new HashSet<>(info.uOut);
		final List<IrNode> nodes = block.getAllNodes();

		final int idx = nodes.indexOf(node);
		if (idx == -1)
			throw new RuntimeException("Invalid instruction.");

		for (int i = nodes.size() - 1; i > idx; i--) {
			final IrNode instr = nodes.get(i);
			final List<Use> localUses = info.uses.get(instr);
			if (localUses != null)
				uses.addAll(localUses);
		}

		return uses;
	}

	/**
	 * Returns all definitions in a block
	 *
	 * @param block
	 *            A block
	 *
	 * @return
	 */
	public Collection<Definition> getBlockDefines(final BasicBlock block) {
		return Collections.unmodifiableCollection(this.blocks.get(block).defs.values());
	}

	/**
	 * Builds a new UD-chain from a function
	 *
	 * @param function
	 *            The function to build the chain for
	 *
	 * @return A UseDefineChain instance
	 */
	public static UseDefineChain buildChain(final Function function) {
		final VariableFinderVisitor varFinder = new VariableFinderVisitor();
		final Map<BasicBlock, BlockInfo> blocks = new HashMap<>();
		final List<Definition> allDefs = new ArrayList<>();
		final List<Use> allUses = new ArrayList<>();

		/* Find all uses and definitions for each block */
		for (final BasicBlock block : function.getBlocksDFS()) {
			final BlockInfo info = new BlockInfo(block);

			final List<Definition> defs = new ArrayList<>();

			for (final IrNode node : block.getNodes()) {
				final Set<VarDecl<? extends Type>> usedVars = new HashSet<>();
				if (node instanceof AssignNode<?, ?>) {
					final AssignNode<?, ?> assign = (AssignNode<?, ?>) node;

					// Add this assignment to definitions
					final Definition def = new Definition(assign.getVar(), assign);

					defs.add(def);
					info.gen.add(def);
					info.defs.put(assign, def);

					// Find all uses
					assign.getExpr().accept(varFinder, usedVars);

					if (!usedVars.isEmpty()) {
						info.uses.put(assign, new ArrayList<Use>());
						usedVars.forEach(v -> {
							final Use use = new Use(assign, v);
							info.uses.get(assign).add(use);
							allUses.add(use);
						});
					}
				} else if (node instanceof AssertNode) {
					final AssertNode assrt = (AssertNode) node;

					assrt.getCond().accept(varFinder, usedVars);
					if (!usedVars.isEmpty()) {
						info.uses.put(assrt, new ArrayList<Use>());
						usedVars.forEach(v -> {
							final Use use = new Use(assrt, v);
							info.uses.get(assrt).add(use);
							allUses.add(use);
						});
					}
				}
			}

			if (block.getTerminator() instanceof ConditionalTerminatorNode) {
				final Set<VarDecl<? extends Type>> usedVars = new HashSet<>();
				final ConditionalTerminatorNode term = (ConditionalTerminatorNode) block.getTerminator();

				term.getCondition().accept(varFinder, usedVars);

				if (!usedVars.isEmpty()) {
					info.uses.put(term, new ArrayList<Use>());
					usedVars.forEach(v -> {
						final Use use = new Use(term, v);
						info.uses.get(term).add(use);
						allUses.add(use);
					});
				}
			}

			allDefs.addAll(defs);
			blocks.put(block, info);
		}

		/* Compute initial sets */
		for (final BlockInfo info : blocks.values()) {
			final List<VarDecl<? extends Type>> vars = info.gen.stream() // Get
																			// a
																			// list
																			// of
																			// all
																			// variables
																			// defined
																			// in
																			// this
																			// block
					.map(d -> d.var).collect(Collectors.toList());
			final List<Definition> defs = allDefs.stream() // Find all
															// definitions which
															// define the
															// variables of this
															// block
					.filter(d -> vars.contains(d.var)).collect(Collectors.toList());

			// A definition is killed in this block, if it's not defined here
			// but defines a variable also defined here
			info.kill.addAll(defs);
			info.kill.removeAll(info.gen);

			// use[B] is a set of (s, x) pairs in B, such...
			info.use.addAll(allUses.stream().filter(u -> info.block.getAllNodes().contains(u.node)) // ...s
																									// is
																									// in
																									// B...
					.filter(u -> {
						final List<Definition> useDefs = defs.stream().filter(d -> d.var == u.var)
								.filter(d -> d.node.getParentBlock() == info.block).collect(Collectors.toList());
						if (useDefs.isEmpty()) // ...and there is no definition
												// of x in B...
							return true;

						// ...or if there is, it is not prior X
						final List<IrNode> nodes = u.node.getParentBlock().getAllNodes();
						final int idx = nodes.indexOf(u.node);
						for (final Definition def : useDefs) {
							if (nodes.indexOf(def.node) < idx) {
								return false;
							}
						}

						return true;
					}).collect(Collectors.toSet()));

			// def[B] is a set of (s, x) pairs, such...
			info.def.addAll(allUses.stream().filter(u -> !info.block.getAllNodes().contains(u.node)) // ...s
																										// is
																										// not
																										// in
																										// B...
					.filter(u -> vars.contains(u.var)) // ...and there is a
														// definition of x in B
					.collect(Collectors.toSet()));
		}

		/*
		 * Iterative solution for reaching definitions. (Compilers: Principles,
		 * Techniques and Tools, 1st edition, Algorithm 10.2)
		 */
		for (final BlockInfo blockInfo : blocks.values()) {
			blockInfo.out.addAll(blockInfo.gen);
		}

		boolean change = true;
		while (change) {
			change = false;
			for (final BlockInfo blockInfo : blocks.values()) {
				/* in[B] = for all p in parent(B) Union {out[p]} */
				final Set<Definition> newIn = new HashSet<>();
				blockInfo.block.parents().forEach(s -> {
					newIn.addAll(blocks.get(s).out);
				});
				blockInfo.in = newIn;

				/* out[B] = gen[B] union (in[B] sub kill[B]) */
				final Set<Definition> newOut = new HashSet<>(blockInfo.gen);
				newOut.addAll(
						blockInfo.in.stream().filter(s -> !blockInfo.kill.contains(s)).collect(Collectors.toSet()));

				if (!blockInfo.out.equals(newOut)) {
					blockInfo.out = newOut;
					change = true;
				}
			}
		}

		return new UseDefineChain(blocks);
	}

}
