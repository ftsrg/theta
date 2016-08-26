package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;

/**
 * A graph representing a dominator tree
 *
 * @author Gyula Sallai
 */
public class DominatorTree {

	private final Map<BasicBlock, BasicBlock> edges;
	private final Function function;
	private final BasicBlock root;

	/**
	 * Initializes a new dominator tree
	 *
	 * @param function The function representing this tree
	 */
	private DominatorTree(Function function, BasicBlock root) {
		this.function = function;
		this.root = root;
		this.edges = new HashMap<>();
	}

	/**
	 * Tells whether A immediately dominates B (whether A is the parent of B)
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a immediately dominates b, false otherwise
	 */
	public boolean immediatelyDominates(BasicBlock a, BasicBlock b) {
		return this.edges.get(b) == a;
	}


	/**
	 * Tells whether A dominates B
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a dominates b, false otherwise
	 */
	public boolean dominates(BasicBlock a, BasicBlock b) {
		BasicBlock current = b;
		while (current != null) {
			if (current == a)
				return true;

			current = this.edges.get(current);
		}

		return false;
	}

	/**
	 * Tells whether A strictly dominates B (A dominates B and A != B)
	 *
	 * @param a The dominator node
	 * @param b The dominated node
	 *
	 * @return True if a strictly dominates b, false otherwise
	 */
	public boolean strictlyDominates(BasicBlock a, BasicBlock b) {
		if (a == b)
			return false;

		return this.dominates(a, b);
	}

	/**
	 * Creates a new dominator tree edge.
	 *
	 * @param from The edge parent
	 * @param to The child
	 */
	public void createEdge(BasicBlock from, BasicBlock to) {
		this.edges.put(to, from);
	}

	/**
	 * Constructs a new dominator tree from a given function
	 *
	 * @param function A function to calculate dominators for
	 *
	 * @return A dominator tree instance
	 */
	public static DominatorTree createDominatorTree(Function function) {
		return createTree(function, false);
	}

	/**
	 * Constructs a new post dominator tree from a given function
	 *
	 * @param function A function to calculate post dominators for
	 *
	 * @return A dominator tree instance
	 */
	public static DominatorTree createPostDominatorTree(Function function) {
		return createTree(function, true);
	}

	/**
	 * Returns the function described by this tree
	 *
	 * @return A function instance
	 */
	public Function getFunction() {
		return this.function;
	}

	/**
	 * Returns the tree root block
	 *
	 * @return A BasicBlock which dominates all nodes in this tree
	 */
	public BasicBlock getRoot() {
		return this.root;
	}

	/**
	 * Returns  the immediate dominator (i.e. the parent) of a given block
	 *
	 * @param block A BasicBlock instance
	 *
	 * @return A block which immediately dominates the given block
	 */
	public BasicBlock getParent(BasicBlock block) {
		return this.edges.get(block);
	}

	/**
	 * Constructs a new (post)dominator tree instance from a given instance
	 *
	 * @param function	The function to calculate (post)dominators for
	 * @param reverse Whether to create a post or predominator tree
	 *
	 * @return A dominator tree instance
	 */
	private static DominatorTree createTree(Function function, boolean reverse) {
		Map<BasicBlock, Set<BasicBlock>> dom = new HashMap<>();
		BasicBlock entry = reverse ? function.getExitBlock() : function.getEntryBlock();

		/*
		 * Calculate dominators using data-flow equations.
		 *
		 * Source: Compilers, principles, techniques and tools, 1st edition.
		 *
		 * D(n0) := {n0}
		 * for n in N \ {n0} do D(n) := N;
		 *
		 * while changes to any D(n) occur do
		 * 	for n in N \ {n0} do
		 * 	  D(n) := {n} union {for all p in parents(n) intersect D(p)}
		 */

		// D[n0] := {n0}
		dom.put(entry, new LinkedHashSet<>());
		dom.get(entry).add(entry);

		// for n in N \ {n0} do D[n] := N
		List<BasicBlock> blocks = function.getBlocks().stream().filter(b -> b != entry).collect(Collectors.toList());
		blocks.forEach(block -> dom.put(block, new LinkedHashSet<>(function.getBlocks())));

		boolean change = true;
		while (change) {
			change = false;
			for (BasicBlock block : blocks) {
				Set<BasicBlock> blockDoms = new LinkedHashSet<>();
				blockDoms.add(block);

				Iterator<BasicBlock> iter = reverse ? block.children().iterator() : block.parents().iterator();

				if (!iter.hasNext())
					throw new RuntimeException("Cannot find any " + (reverse ? "children" : "parents") + " of block '" + block.getName() + "'");

				BasicBlock first = iter.next();
				Set<BasicBlock> parentDoms = new LinkedHashSet<>(dom.get(first));
				while (iter.hasNext()) {
					BasicBlock next = iter.next();
					parentDoms.retainAll(dom.get(next));
				}

				blockDoms.addAll(parentDoms);

				if (!dom.get(block).equals(blockDoms)) {
					dom.put(block, blockDoms);
					change = true;
				}
			}
		}

		DominatorTree dt = new DominatorTree(function, entry);

		// Find immediate dominators
		dom.forEach((BasicBlock block, Set<BasicBlock> dominators) -> {
			// block: The block being checked
			// dominators: The dominators of this block
			// idom: The block's immediate dominator
			BasicBlock idom = null;
			for (BasicBlock dominator : dominators) {
				boolean isIdom = true;

				if (dominator == block)
					continue;

				List<BasicBlock> otherDoms = dominators.stream().filter(s -> s != block && s != dominator).collect(Collectors.toList());
				for (BasicBlock od : otherDoms) {
					if (!dom.get(dominator).contains(od)) {
						isIdom = false;
						break;
					}
				}

				if (isIdom) {
					idom = dominator;
					break;
				}
			}

			dt.createEdge(idom, block);
		});

		return dt;
	}
}
