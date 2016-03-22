package hu.bme.mit.inf.ttmc.cegar.clusteredcegar.data;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystemBase;
import hu.bme.mit.inf.ttmc.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Represents the clustered abstract system.
 *
 * @author Akos
 */
public class ClusteredAbstractSystem extends AbstractSystemBase {

	private final List<Expr<? extends BoolType>> atomicFormulas; // Atomic formulas in the conditions and the specification
	private final List<Cluster> clusters; // Clusters (variables and formulas)
	private final List<KripkeStructure<ComponentAbstractState>> abstractKripkeStructures; // Abstract Kripke structure for each cluster

	public ClusteredAbstractSystem(final STS system) {
		super(system);
		this.atomicFormulas = new ArrayList<>();
		this.clusters = new ArrayList<>();
		this.abstractKripkeStructures = new ArrayList<>();
	}

	/**
	 * Get the list of atomic formulas in the conditions and the specification
	 *
	 * @return List of atomic formulas in the conditions and the specification
	 */
	public List<Expr<? extends BoolType>> getAtomicFormulas() {
		return atomicFormulas;
	}

	/**
	 * Get the list of clusters
	 *
	 * @return List of clusters
	 */
	public List<Cluster> getClusters() {
		return clusters;
	}

	/**
	 * Get the list of abstract Krikpe structures
	 *
	 * @return List of abstract Kripke structures
	 */
	public List<KripkeStructure<ComponentAbstractState>> getAbstractKripkeStructures() {
		return abstractKripkeStructures;
	}

	/**
	 * Get the ith abstract Kripke Structure
	 *
	 * @param i
	 *            Index
	 * @return ith abstract Kripke Structure
	 */
	public KripkeStructure<ComponentAbstractState> getAbstractKripkeStructure(final int i) {
		return abstractKripkeStructures.get(i);
	}

}
