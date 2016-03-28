package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystemBase;
import hu.bme.mit.inf.ttmc.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Represents the interpolated abstract system.
 */
public class InterpolatedAbstractSystem extends AbstractSystemBase {

	private final List<Expr<? extends BoolType>> initialPredicates;
	private KripkeStructure<InterpolatedAbstractState> abstractKripkeStructure;
	private final Set<VarDecl<? extends Type>> explicitVars;
	private final Set<VarDecl<? extends Type>> vars;
	private final Set<VarDecl<? extends Type>> cnfVars;
	private int previousSplitIndex; // Index of the first state (in the counterexample) that was split in the previous iteration

	public InterpolatedAbstractSystem(final STS system) {
		super(system);
		initialPredicates = new ArrayList<>();
		abstractKripkeStructure = null;
		cnfVars = new HashSet<>();
		explicitVars = new HashSet<>();
		vars = new HashSet<>();
		previousSplitIndex = -1;
	}

	public List<Expr<? extends BoolType>> getInitialPredicates() {
		return initialPredicates;
	}

	public KripkeStructure<InterpolatedAbstractState> getAbstractKripkeStructure() {
		return abstractKripkeStructure;
	}

	public void setAbstractKripkeStructure(final KripkeStructure<InterpolatedAbstractState> abstractKripkeStructure) {
		this.abstractKripkeStructure = abstractKripkeStructure;
	}

	public Set<VarDecl<? extends Type>> getCNFVariables() {
		return this.cnfVars;
	}

	@Override
	public Set<VarDecl<? extends Type>> getVars() {
		return this.vars;
	}

	public Set<VarDecl<? extends Type>> getExplicitVariables() {
		return this.explicitVars;
	}

	public int getPreviousSplitIndex() {
		return previousSplitIndex;
	}

	public void setPreviousSplitIndex(final int lastSplitIndex) {
		this.previousSplitIndex = lastSplitIndex;
	}
}
