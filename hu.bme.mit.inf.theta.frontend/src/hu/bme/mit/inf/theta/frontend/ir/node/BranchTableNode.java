package hu.bme.mit.inf.theta.frontend.ir.node;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;

/**
 * This terminator node allows multiple branched targets from a condition node
 */
public class BranchTableNode implements TerminatorIrNode {

	public static class BranchTableEntry {
		private Expr<? extends Type> value;
		private BasicBlock target;

		public BranchTableEntry(Expr<? extends Type> value, BasicBlock target) {
			this.value = value;
			this.target = target;
		}

		public Expr<? extends Type> getValue() {
			return this.value;
		}

		public BasicBlock getTarget() {
			return this.target;
		}
	}

	//private final Map<Expr<? extends Type>, BasicBlock> targets = new HashMap<>();
	private final List<BranchTableEntry> targets = new ArrayList<>();

	private Expr<? extends Type> condition;
	private BasicBlock defaultTarget;

	private BasicBlock parent;

	public BranchTableNode(Expr<?> condition) {
		this.condition = condition;
	}

	public void addTarget(Expr<?> condition, BasicBlock target) {
		this.targets.add(new BranchTableEntry(condition, target));
	}

	public BasicBlock getTargetFromValue(Expr<? extends Type> condition) {
		return this.targets
			.stream()
			.filter(t -> t.value.equals(condition))
			.findFirst()
			.map(t -> t.target)
			.orElseThrow(() -> new RuntimeException("The value " + condition + " was not found in the branch table."));
	}

	public Expr<? extends Type> getValueFromTarget(BasicBlock target) {
		return this.targets
			.stream()
			.filter(t -> t.target == target)
			.findFirst()
			.map(t -> t.value)
			.orElseThrow(() -> new RuntimeException("The target " + target.getName() + " was not found in the branch table."));
	}

	@Override
	public void replaceTarget(BasicBlock oldTarget, BasicBlock newTarget) {
		if (oldTarget == this.defaultTarget) {
			this.defaultTarget.removeParent(this.parent);
			this.defaultTarget = newTarget;
			this.defaultTarget.addParent(this.parent);
		} else {
			Expr<? extends Type> val = this.getValueFromTarget(oldTarget);
			this.targets.removeIf(t -> t.target == oldTarget);
			oldTarget.removeParent(this.parent);

			this.targets.add(new BranchTableEntry(val, newTarget));
			newTarget.addParent(this.parent);
		}
	}


	public List<BranchTableEntry> getValueEntries() {
		return Collections.unmodifiableList(this.targets);
	}

	/**
	 * Returns the size of the branch table, without the default path.
	 *
	 * @return The branch table size
	 */
	public int getEntryCount() {
		return this.targets.size();
	}

	public void setCondition(Expr<? extends Type> expr) {
		this.condition = expr;
	}

	public Expr<? extends Type> getCondition() {
		return this.condition;
	}

	public BasicBlock getDefaultTarget() {
		return defaultTarget;
	}

	public void setDefaultTarget(BasicBlock defaultTarget) {
		this.defaultTarget = defaultTarget;
	}

	@Override
	public String getLabel() {
		return "Switch(" + this.condition + ")";
	}

	@Override
	public TerminatorIrNode copy() {
		throw new UnsupportedOperationException("duh");
	}

	@Override
	public void setParentBlock(BasicBlock block) {
		this.parent = block;
	}

	@Override
	public BasicBlock getParentBlock() {
		return this.parent;
	}

	@Override
	public List<BasicBlock> getTargets() {
		List<BasicBlock> targets = this.targets
			.stream()
			.map(t -> t.target)
			.collect(Collectors.toList());

		targets.add(this.defaultTarget);

		return targets;
	}

}
