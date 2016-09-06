package hu.bme.mit.inf.theta.cegar.clusteredcegar.data;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.theta.cegar.common.data.AbstractSystemBase;
import hu.bme.mit.inf.theta.cegar.common.data.KripkeStructure;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.sts.STS;

public class ClusteredAbstractSystem extends AbstractSystemBase {

	private final List<Expr<? extends BoolType>> atomicFormulas;
	private final List<Cluster> clusters;
	private final List<KripkeStructure<ComponentAbstractState>> abstractKripkeStructures;

	public ClusteredAbstractSystem(final STS system) {
		super(system);
		this.atomicFormulas = new ArrayList<>();
		this.clusters = new ArrayList<>();
		this.abstractKripkeStructures = new ArrayList<>();
	}

	public List<Expr<? extends BoolType>> getAtomicFormulas() {
		return atomicFormulas;
	}

	public List<Cluster> getClusters() {
		return clusters;
	}

	public List<KripkeStructure<ComponentAbstractState>> getAbstractKripkeStructures() {
		return abstractKripkeStructures;
	}

	public KripkeStructure<ComponentAbstractState> getAbstractKripkeStructure(final int i) {
		checkArgument(0 <= i && i < abstractKripkeStructures.size());
		return abstractKripkeStructures.get(i);
	}

}
