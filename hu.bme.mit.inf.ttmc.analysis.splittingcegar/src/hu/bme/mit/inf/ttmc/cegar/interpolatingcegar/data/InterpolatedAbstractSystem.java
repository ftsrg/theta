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
 *
 * @author Akos
 */
public class InterpolatedAbstractSystem extends AbstractSystemBase {

	private final List<Expr<? extends BoolType>> initialPredicates; // Initial predicates for the predicate abstraction
	private KripkeStructure<InterpolatedAbstractState> abstractKripkeStructure; // Abstract Kripke structure of the system
	private final Set<VarDecl<? extends Type>> explicitVariables; // Explicitly tracked variables
	private final Set<VarDecl<? extends Type>> variables; // Non-CNF variables
	private final Set<VarDecl<? extends Type>> cnfVariables; // Variables introduced by the CNF (Tseitin) transformation
	private int previousSplitIndex; // Index of the first state (in the counterexample) that was split in the previous iteration

	/**
	 * Constructor
	 *
	 * @param problem
	 *            Problem
	 */
	public InterpolatedAbstractSystem(final STS system) {
		super(system);
		initialPredicates = new ArrayList<>();
		abstractKripkeStructure = null;
		cnfVariables = new HashSet<>();
		explicitVariables = new HashSet<>();
		variables = new HashSet<>();
		previousSplitIndex = -1;
	}

	/**
	 * Get the initial predicates
	 *
	 * @return
	 * @return Initial predicates
	 */
	public List<Expr<? extends BoolType>> getInitialPredicates() {
		return initialPredicates;
	}

	/**
	 * Get the abstract Kripke structure
	 *
	 * @return Abstract Kripke structure
	 */
	public KripkeStructure<InterpolatedAbstractState> getAbstractKripkeStructure() {
		return abstractKripkeStructure;
	}

	/**
	 * Set the abstract Kripke structure
	 *
	 * @param abstractKripkeStructure
	 *            Abstract Kripke structure
	 */
	public void setAbstractKripkeStructure(final KripkeStructure<InterpolatedAbstractState> abstractKripkeStructure) {
		this.abstractKripkeStructure = abstractKripkeStructure;
	}

	/**
	 * Get the list of variables introduced by the CNF (Tseitin) transformation
	 *
	 * @return List of CNF variables
	 */
	public Set<VarDecl<? extends Type>> getCNFVariables() {
		return this.cnfVariables;
	}

	@Override
	public Set<VarDecl<? extends Type>> getVariables() {
		return this.variables;
	}

	public Set<VarDecl<? extends Type>> getExplicitVariables() {
		return this.explicitVariables;
	}

	/**
	 * Get the index of the first state (in the counterexample) that was split
	 * in the previous iteration
	 *
	 * @return Index
	 */
	public int getPreviousSplitIndex() {
		return previousSplitIndex;
	}

	/**
	 * Set the index of the first state (in the counterexample) that was split
	 * in the previous iteration
	 *
	 * @param lastSplitIndex
	 *            Index
	 */
	public void setPreviousSplitIndex(final int lastSplitIndex) {
		this.previousSplitIndex = lastSplitIndex;
	}
}
