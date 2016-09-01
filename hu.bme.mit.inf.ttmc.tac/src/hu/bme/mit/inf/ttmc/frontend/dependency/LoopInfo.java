package hu.bme.mit.inf.ttmc.frontend.dependency;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.Stack;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.frontend.ir.BasicBlock;
import hu.bme.mit.inf.ttmc.frontend.ir.Function;

public class LoopInfo {

	private final List<BasicBlock> blocks;
	private final BasicBlock header;
	private final DominatorTree domTree;


	private final Optional<BasicBlock> preHeader;

	protected LoopInfo(BasicBlock header, List<BasicBlock> blocks, DominatorTree dt) {
		this.header = header;
		this.blocks = blocks;
		this.domTree = dt;

		List<BasicBlock> preHeaderCandidates = this.header.parents()
			.stream()
			.filter(parent -> !this.blocks.contains(parent))
			.collect(Collectors.toList());

		if (preHeaderCandidates.size() == 1) {
			this.preHeader = Optional.of(preHeaderCandidates.get(0));
		} else {
			this.preHeader = Optional.empty();
		}
	}

	/**
	 * Returns the header block of this loop
	 *
	 * @return A BasicBlock dominating all nodes in this loop
	 */
	public BasicBlock getHeader() {
		return this.header;
	}

	/**
	 * Returns a list of blocks which make up this loop.
	 *
	 * @return A list of BasicBlocks
	 */
	public List<BasicBlock> getBlocks() {
		return Collections.unmodifiableList(this.blocks);
	}

	/**
	 * Returns all blocks which have an edge pointing out from the loop
	 *
	 * @return A list of basic blocks
	 */
	public List<BasicBlock> getExists() {
		return this.blocks
			.stream()
			.filter(block -> block.children().stream().filter(child -> !this.blocks.contains(child)).count() != 0)
			.collect(Collectors.toList());
	}

	/**
	 * Tells whether this loop has a preheader.
	 *
	 * A block is the preheader of a loop if it is the only parent of the loop header outside the loop
	 *
	 * @return True if the loop has a preheader, false otherwise
	 */
	public boolean hasPreHeader() {
		return this.preHeader.isPresent();
	}

	/**
	 * Returns a list of natural loops contained in a given function.
	 *
	 * @param function The function to analyze
	 *
	 * @return A list of LoopInfo instances, describing loops in function
	 */
	public static List<LoopInfo> findLoops(Function function) {
		DominatorTree dt = DominatorTree.createDominatorTree(function);
		List<BasicBlock> blocks = function.getBlocksDFS();
		List<LoopInfo> result = new ArrayList<>();

		for (BasicBlock block : blocks) {
			List<BasicBlock> backEdges = new ArrayList<>();
			for (BasicBlock parent : block.parents()) {
				if (dt.dominates(block, parent)) {
					backEdges.add(parent);
				}
			}

			if (!backEdges.isEmpty()) {
				List<BasicBlock> loopBlocks = new ArrayList<>();
				final BasicBlock header = block;

				// Perform a reverse DFS search for loop blocks
				for (BasicBlock tail : backEdges) {
					Stack<BasicBlock> queue = new Stack<>();
					queue.push(tail);

					while (!queue.isEmpty()) {
						BasicBlock current = queue.pop();
						if (!loopBlocks.contains(current) && dt.dominates(header, current)) {
							loopBlocks.add(current);
							for (BasicBlock parent : current.parents()) {
								queue.push(parent);
							}
						}
					}
				}

				result.add(new LoopInfo(header, loopBlocks, dt));
			}
		}

		return result;
	}


}
