package hu.bme.mit.theta.frontend.c.transform.slicer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.c.ir.BasicBlock;
import hu.bme.mit.theta.frontend.c.ir.Function;
import hu.bme.mit.theta.frontend.c.ir.node.ConditionalTerminatorNode;
import hu.bme.mit.theta.frontend.c.ir.node.IrNode;
import hu.bme.mit.theta.frontend.c.transform.slicer.utils.SliceCreator;

public class Slice {

	private final Function original;
	private final IrNode criterion;
	
	private Collection<IrNode> additional;
	
	private Function sliced;
	private Map<BasicBlock, BasicBlock> blockMap;
	
	private Map<ConditionalTerminatorNode, ConditionalTerminatorNode> abstractPreds;
	
	private FunctionSlicer refinementSlicer = new BackwardSlicer();
	
	private Slice(
		Function function,
		Function sliced,
		Map<BasicBlock, BasicBlock> blockMap,
		IrNode criterion,
		Map<ConditionalTerminatorNode, ConditionalTerminatorNode> abstractPreds,
		Collection<IrNode> additional
	) {
		this.original = function;
		this.sliced = sliced;
		this.blockMap = blockMap;
		this.criterion = criterion;
		this.abstractPreds = abstractPreds;
		this.additional = additional;
	}	
		
	public void setRefinementSlicer(FunctionSlicer slicer) {
		this.refinementSlicer = slicer;
	}
	
	public void copyFrom(Slice other) {
		this.sliced = other.sliced;
		this.blockMap = other.blockMap;
		this.abstractPreds = other.abstractPreds;
		this.additional = other.additional;
	}
	
	public boolean canRefine() {
		return !this.abstractPreds.isEmpty();
	}
	
	public void refine() {
		ConditionalTerminatorNode refinedNode = this.pickRefinedNode();
			
		List<IrNode> adds = new ArrayList<IrNode>(this.additional);
		adds.add(refinedNode);
		
		Slice refined = this.refinementSlicer.slice(this.original, this.criterion, adds);
		this.copyFrom(refined);
	}
	
	protected ConditionalTerminatorNode pickRefinedNode() {		
		// Currently we just pick a random node for refinement		
		Iterator<Entry<ConditionalTerminatorNode, ConditionalTerminatorNode>> it = this.abstractPreds.entrySet().iterator();
		if (!it.hasNext()) {
			throw new RuntimeException("Unable to refine: no abstract predicates are present.");
		}
		
		return it.next().getKey();
	}

	public Function getSlicedFunction() {
		return this.sliced;
	}
	
	public static SliceBuilder builder(Function function, IrNode criterion) {
		return new SliceBuilder(function, criterion);
	}
	
	public static class SliceBuilder {		
		private Function function;
		private IrNode criterion;
		private List<IrNode> additional = new ArrayList<>();
		
		private Function copy;
		private Map<BasicBlock, BasicBlock> blockMap;
	 	
		private List<IrNode> visited;
		
		private Map<ConditionalTerminatorNode, ConditionalTerminatorNode> abstractPreds = new HashMap<>();
		
		public SliceBuilder(Function function, IrNode criterion) {
			this.function = function;
			this.criterion = criterion;
		}
		
		public void setCopy(Function copy, Map<BasicBlock, BasicBlock> blockMap) {
			this.copy = copy;
			this.blockMap = blockMap;
		}
		
		public void addAbstractPredicate(ConditionalTerminatorNode original, ConditionalTerminatorNode newPred) {
			this.abstractPreds.put(original, newPred);
		}

		public void setVisited(List<IrNode> visited) {
			this.visited = visited;
		}
		
		public void addAdditional(Collection<IrNode> additional) {
			this.additional.addAll(additional);
		}
		
		public Slice build() {
			if (copy == null || blockMap == null || visited == null) {
				throw new RuntimeException("Cannot build slice without a function copy and a set of marked nodes.");
			}
			
			Function sliced = SliceCreator.constructSlice(this.function, this.visited, this.blockMap, this.copy);
			
			return new Slice(this.function, sliced, this.blockMap, this.criterion, this.abstractPreds, this.additional);
		}
		
	}
}

