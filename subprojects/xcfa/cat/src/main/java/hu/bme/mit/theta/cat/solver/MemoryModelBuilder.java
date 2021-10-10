package hu.bme.mit.theta.cat.solver;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public abstract class MemoryModelBuilder {
	private final MemoryModel memoryModel;

	protected MemoryModelBuilder(MemoryModel memoryModel) {
		this.memoryModel = memoryModel;
	}

	private final Map<Object, Integer> indexMap = new EqualityLinkedHashMap<>();
	public void addProgramLoc(Object object) {
		if(!indexMap.containsKey(object)) {
			indexMap.put(object, addPrimitive("meta", object));
		}
	}

	public void addPoEdge(Object a, Object b) {
		final Integer idxA = indexMap.get(a);
		final Integer idxB = indexMap.get(b);
		addFact("poRaw", TupleN.of(idxA, idxB));
	}

	public void addReadProgramLoc(Object read, Object thread, Object var) {
		if(!indexMap.containsKey(read)) {
			indexMap.put(read, addPrimitive("R", read));
		}
		final Integer idxA = indexMap.get(read);
		final Integer idxB = indexMap.get(thread);
		final Integer idxC = indexMap.get(var);
		addFact("intRaw", TupleN.of(idxA, idxB));
		addFact("locRaw", TupleN.of(idxA, idxC));
	}

	public void addWriteProgramLoc(Object write, Object thread, Object var) {
		if(!indexMap.containsKey(write)) {
			indexMap.put(write, addPrimitive("W", write));
		}
		final Integer idxA = indexMap.get(write);
		final Integer idxB = indexMap.get(thread);
		final Integer idxC = indexMap.get(var);
		addFact("intRaw", TupleN.of(idxA, idxB));
		addFact("locRaw", TupleN.of(idxA, idxC));
	}
	public void addFenceLoc(Object write, Object thread) {
		if(!indexMap.containsKey(write)) {
			indexMap.put(write, addPrimitive("F", write));
		}
		final Integer idxA = indexMap.get(write);
		final Integer idxB = indexMap.get(thread);
		addFact("intRaw", TupleN.of(idxA, idxB));
	}
	public Expr<BoolType> addConstraints(final List<Tuple2<?, ConstDecl<?>>> writeConst, final List<Tuple2<?, ConstDecl<?>>> readConst) {
		final List<Tuple2<Integer, ConstDecl<?>>> stores = new ArrayList<>();
		for (Tuple2<?, ConstDecl<?>> objects : writeConst) {
			final Object object = objects.get1();
			final Integer idxS = indexMap.get(object);
			stores.add(Tuple2.of(idxS, objects.get2()));
		}
		final List<Tuple2<Integer, ConstDecl<?>>> loads = new ArrayList<>();
		for (Tuple2<?, ConstDecl<?>> objects : readConst) {
			final Object object = objects.get1();
			final Integer idxR = indexMap.get(object);
			loads.add(Tuple2.of(idxR, objects.get2()));
		}
		return getRfConstraints(stores, loads);
	}

	public abstract List<TupleN<?>> get(final String rule, final Valuation valuation);
	public abstract List<TupleN<Integer>> getNumbered(final String rule, final Valuation valuation);
	public abstract void assertAcyclic(final String ruleDerivation);
	public abstract void assertIrreflexive(final String ruleDerivation);
	public abstract void assertEmpty(final String ruleDerivation);
	public abstract void addRule(final RuleDerivation ruleDerivation);
	public abstract void addFact(final String name, final TupleN<Integer> fact);
	public abstract int addPrimitive(final String name, final Object primitive);
	public abstract Expr<BoolType> getRfConstraints(final List<Tuple2<Integer, ConstDecl<?>>> writeConst, final List<Tuple2<Integer, ConstDecl<?>>> readConst);

	public abstract MemoryModelBuilder duplicate();
}
