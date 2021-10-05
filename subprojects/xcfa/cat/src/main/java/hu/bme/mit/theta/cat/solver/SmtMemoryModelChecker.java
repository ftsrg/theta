package hu.bme.mit.theta.cat.solver;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.functype.FuncExprs;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Xor;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class SmtMemoryModelChecker implements MemoryModelSolver<Object, Object> {
	private static final FuncType<IntType, BoolType> unaryPredicate  = FuncExprs.Func(Int(), Bool());
	private static final FuncType<IntType, FuncType<IntType, BoolType>> binaryPredicate = FuncExprs.Func(Int(), FuncExprs.Func(Int(), Bool()));

	private final List<List<Tuple2<Object, Object>>> rf;
	private SmtMemoryModelChecker(final Builder builder) {
		this.rf = new ArrayList<>();

		final ParamDecl<IntType> a = builder.a;
		final ParamDecl<IntType> b = builder.b;
		final Solver solver = builder.solver;

		final int maxId = builder.factIdxLut.size() - 1;
		final Expr<BoolType> binaryRange = And(List.of(
				Geq(a.getRef(), Int(0)),
				Geq(b.getRef(), Int(0)),
				Leq(a.getRef(), Int(maxId)),
				Leq(b.getRef(), Int(maxId))
		));
		final Expr<BoolType> unaryRange = And(List.of(
				Geq(a.getRef(), Int(0)),
				Leq(a.getRef(), Int(maxId))
		));

		for (IteExpr<BoolType> assumption : builder.binaryAssumptions) {
			final Expr<BoolType> simplified = ExprUtils.simplify(Forall(List.of(a, b), assumption.withCond(binaryRange)));
			System.err.println("Adding assumption: " + simplified);
			solver.add(simplified);
		}
		for (IteExpr<BoolType> assumption : builder.unaryAssumptions) {
			final Expr<BoolType> simplified = ExprUtils.simplify(Forall(List.of(a), assumption.withCond(unaryRange)));
			System.err.println("Adding assumption: " + simplified);
			solver.add(simplified);
		}

		for (Expr<BoolType> nullaryAssumption : builder.nullaryAssumptions) {
			final Expr<BoolType> simplified = ExprUtils.simplify(nullaryAssumption);
			System.err.println("Adding assumption: " + simplified);
			solver.add(simplified);
		}

		for (Map.Entry<String, Expr<BoolType>> entry : builder.facts.entrySet()) {
			final String s = entry.getKey();
			final Expr<BoolType> boolTypeExpr = entry.getValue();
			Expr<BoolType> assumption;
			if(builder.unaryRelations.containsKey(s)) {
				final Decl<FuncType<IntType, BoolType>> rel = builder.unaryRelations.get(s);
				assumption = Forall(List.of(a), Ite(unaryRange, Eq(App(rel.getRef(), a.getRef()), boolTypeExpr), Not(App(rel.getRef(), a.getRef()))));
			} else if (builder.binaryRelations.containsKey(s)) {
				final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> rel = builder.binaryRelations.get(s);
				assumption = Forall(List.of(a, b), Ite(binaryRange, Eq(App(App(rel.getRef(), a.getRef()), b.getRef()), boolTypeExpr), Not(App(App(rel.getRef(), a.getRef()), b.getRef()))));
			} else throw new RuntimeException("Relation " + s + " does not exist.");
			final Expr<BoolType> simplified = ExprUtils.simplify(assumption);
			System.err.println("Adding assumption: " + simplified);
			solver.add(simplified);
		}

//		solver.check();
//		while(solver.getStatus().isSat()) {
//			final Map<Decl<?>, LitExpr<?>> valuation = solver.getModel().toMap();
//			final List<Tuple2<Object, Object>> currentRf = new ArrayList<>();
//			Expr<BoolType> ref = True();
//			for (Map.Entry<Tuple2<Decl<IntType>, Object>, Integer> entry : builder.reads.entrySet()) {
//				Tuple2<Decl<IntType>, Object> objects = entry.getKey();
//				final Object read = objects.get2();
//				final IntLitExpr value = (IntLitExpr) cast(valuation.get(objects.get1()), Int());
//				final int idx = (int) value.getValue().longValue();
//				final Object write = builder.idxFactLut.get(idx);
//				currentRf.add(Tuple2.of(write, read));
//				ref = And(ref, Eq(objects.get1().getRef(), value));
//			}
//			rf.add(currentRf);
//			System.err.println("Found new set of rf-edges:");
//			printOneRfSet(currentRf);
//			solver.add(Not(ref));
//			solver.check();
//		}
	}

	private void printOneRfSet(List<Tuple2<Object, Object>> objectObjectMap) {
		for (Tuple2<Object, Object> entry : objectObjectMap) {
			Object o = entry.get1();
			Object o2 = entry.get2();
			System.out.println("rf(" + o + " -> " + o2 + ")");
		}
		System.out.println("=======END-SET=======");
	}

	public static Builder builder(Solver solver) {
		return new Builder(solver);
	}

	@Override
	public Collection<? extends Collection<Tuple2<Object, Object>>> getAllRf() {
		return rf;
	}

	public static class Builder implements ProgramBuilder<Object, Object, Object> {
		private final Map<String, Decl<FuncType<IntType, FuncType<IntType, BoolType>>>> binaryRelations;
		private final Map<String, Decl<FuncType<IntType, BoolType>>> unaryRelations;
		private final Map<Object, Integer> factIdxLut;
		private final Map<Integer, Object> idxFactLut;
		private final List<IteExpr<BoolType>> binaryAssumptions;
		private final List<IteExpr<BoolType>> unaryAssumptions;
		private final List<Expr<BoolType>> nullaryAssumptions;
		private final Map<Tuple2<Decl<IntType>, Object>, Integer> reads;
		private final Map<Object, Integer> writes;
		private final Map<String, Expr<BoolType>> facts;
		private final ParamDecl<IntType> a;
		private final ParamDecl<IntType> b;
		private final Solver solver;

		private Builder(final Solver solver) {
			this.solver = solver;
			binaryAssumptions = new ArrayList<>();
			unaryAssumptions = new ArrayList<>();
			nullaryAssumptions  = new ArrayList<>();
			reads = new EqualityLinkedHashMap<>();
			writes = new EqualityLinkedHashMap<>();
			factIdxLut = new EqualityLinkedHashMap<>();
			idxFactLut = new EqualityLinkedHashMap<>();
			facts = new EqualityLinkedHashMap<>();
			binaryRelations = new EqualityLinkedHashMap<>();
			unaryRelations  = new EqualityLinkedHashMap<>();

			a = Param("a", Int());
			b = Param("b", Int());

			final Decl<FuncType<IntType, BoolType>> meta = createUnaryPredicate("meta");

			final Decl<FuncType<IntType, BoolType>> fence = createUnaryPredicate("F");
			final Decl<FuncType<IntType, BoolType>> write = createUnaryPredicate("W");
			final Decl<FuncType<IntType, BoolType>> read = createUnaryPredicate("R");

			final Decl<FuncType<IntType, BoolType>> memory = createUnaryPredicate("M");

			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> poRaw = createBinaryRelation("poRaw");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> locRaw = createBinaryRelation("locRaw");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> intRaw = createBinaryRelation("intRaw");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> amoRaw = createBinaryRelation("amoRaw");


			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> id = createBinaryRelation("id");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> po = createBinaryRelation("po");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> rf = createBinaryRelation("rf");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> co = createBinaryRelation("co");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> fr = createBinaryRelation("fr");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> loc = createBinaryRelation("loc");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> in = createBinaryRelation("int");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> ex = createBinaryRelation("ext");
			final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> amo = createBinaryRelation("amo");

			ParamDecl<IntType> c = Param("c", Int());
			ParamDecl<IntType> d = Param("d", Int());

			// unary derived relations
			createUnaryRule(memory, Or(App(write.getRef(), a.getRef()), App(read.getRef(), a.getRef())));

			// transitive binary relations
			createBinaryRule(po, Or(List.of(
					App(App(poRaw.getRef(), a.getRef()), b.getRef()),
					Exists(List.of(c), And(App(App(poRaw.getRef(), a.getRef()), c.getRef()), App(App(po.getRef(), c.getRef()), b.getRef())))
			)));
			// transitive, reflexive binary relations
			createBinaryRule(loc, Or(List.of(
					Eq(a.getRef(), b.getRef()),
					App(App(locRaw.getRef(), a.getRef()), b.getRef()),
					App(App(locRaw.getRef(), b.getRef()), a.getRef()),
					Exists(List.of(c), And(App(App(locRaw.getRef(), a.getRef()), c.getRef()), App(App(loc.getRef(), c.getRef()), b.getRef())))
			)));
			createBinaryRule(in, Or(List.of(
					App(App(intRaw.getRef(), a.getRef()), b.getRef()),
					App(App(intRaw.getRef(), b.getRef()), a.getRef()),
					Exists(List.of(c), And(App(App(intRaw.getRef(), a.getRef()), c.getRef()), App(App(in.getRef(), c.getRef()), b.getRef())))
			)));
			createBinaryRule(amo, Or(List.of(
					App(App(amoRaw.getRef(), a.getRef()), b.getRef()),
					App(App(amoRaw.getRef(), b.getRef()), a.getRef()),
					Exists(List.of(c), And(App(App(amoRaw.getRef(), a.getRef()), c.getRef()), App(App(amo.getRef(), c.getRef()), b.getRef())))
			)));

			// binary derived relations
			createBinaryRule(id, Eq(a.getRef(), b.getRef()));
			createBinaryRule(fr, Exists(List.of(c), And(App(App(rf.getRef(), c.getRef()), a.getRef()), App(App(co.getRef(), c.getRef()), b.getRef()))));
			createBinaryRule(ex, Not(App(App(in.getRef(), a.getRef()), b.getRef())));

			// co constraint (special case, irreflexivity and location-specific total order)
			createBinaryAssumption(
					Imply(App(App(co.getRef(), a.getRef()), b.getRef()), Not(App(App(co.getRef(), b.getRef()), a.getRef()))),
					Not(App(App(co.getRef(), a.getRef()), b.getRef())));
			createBinaryAssumption(Imply(
					And(List.of(
						Neq(a.getRef(), b.getRef()),
						App(App(loc.getRef(), a.getRef()), b.getRef()),
						App(write.getRef(), a.getRef()),
						App(write.getRef(), b.getRef()))),
					Xor(
						App(App(co.getRef(), a.getRef()), b.getRef()),
						App(App(co.getRef(), b.getRef()), a.getRef()))),
				Not(App(App(co.getRef(), a.getRef()), b.getRef())));

			// read-exactly-once
			createBinaryAssumption(Ite(App(read.getRef(), a.getRef()), And(
					Exists(List.of(c), App(App(rf.getRef(), c.getRef()), a.getRef())),
					Not(Exists(List.of(c, d), And(List.of(
							Neq(c.getRef(), d.getRef()),
							App(App(rf.getRef(), c.getRef()), a.getRef()),
							App(App(rf.getRef(), d.getRef()), a.getRef())))))),
					Not(Exists(List.of(c), App(App(rf.getRef(), c.getRef()), a.getRef())))),
				Not(App(App(rf.getRef(), a.getRef()), b.getRef())));

			createBinaryAssumption(Imply(Not(And(App(write.getRef(), a.getRef()), App(read.getRef(), b.getRef()))), Not(App(App(rf.getRef(), a.getRef()), b.getRef()))), Not(App(App(rf.getRef(), a.getRef()), b.getRef())));
		}

		private Decl<FuncType<IntType, FuncType<IntType, BoolType>>> createBinaryRelation(final String name) {
			final ConstDecl<FuncType<IntType, FuncType<IntType, BoolType>>> rel = Const(name, binaryPredicate);
			binaryRelations.put(name, rel);
			return rel;
		}

		private Decl<FuncType<IntType, BoolType>> createUnaryPredicate(final String name) {
			final ConstDecl<FuncType<IntType, BoolType>> rel = Const(name, unaryPredicate);
			unaryRelations.put(name, rel);
			return rel;
		}

		private void createBinaryRule(final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> rel, final Expr<BoolType> rule) {
			binaryAssumptions.add(Ite(True(), Eq(App(App(rel.getRef(), a.getRef()), b.getRef()), /*ExprUtils.simplify*/(rule)), Not(App(App(rel.getRef(), a.getRef()), b.getRef()))));
		}

		private void createUnaryRule(final Decl<FuncType<IntType, BoolType>> rel, final Expr<BoolType> rule) {
			unaryAssumptions.add(Ite(True(), Eq(App(rel.getRef(), a.getRef()), /*ExprUtils.simplify*/(rule)), Not(App(rel.getRef(), a.getRef()))));
		}

		private void createBinaryAssumption(final Expr<BoolType> inRange, final Expr<BoolType> notInRange) {
			binaryAssumptions.add(/*ExprUtils.simplify*/Ite(True(), inRange, notInRange));
		}

		private void createUnaryAssumption(final Expr<BoolType> inRange, final Expr<BoolType> notInRange) {
			unaryAssumptions.add(/*ExprUtils.simplify*/Ite(True(), inRange, notInRange));
		}

		private int addUnaryFact(final String name, Object object) {
			if(factIdxLut.containsKey(object)) return factIdxLut.get(object);
			int currentSize = factIdxLut.size();
			factIdxLut.put(object, currentSize);
			idxFactLut.put(currentSize, object);
			facts.put(name, /*ExprUtils.simplify*/(Or(facts.getOrDefault(name, False()), Eq(a.getRef(), Int(currentSize)))));
			if(name.equals("R")) {
				reads.put(Tuple2.of(Const("R" + reads.size(), Int()), object), currentSize);
			} else if (name.equals("W")) {
				writes.put(object, currentSize);
			}
			return currentSize;
		}

		private void addBinaryFact(final String name, final Object obj1, final Object obj2) {
			checkArgument(factIdxLut.containsKey(obj1) && factIdxLut.containsKey(obj2), "Facts of a relation have to be added manually!");
			final int idx1 = factIdxLut.get(obj1);
			final int idx2 = factIdxLut.get(obj2);
			facts.put(name, /*ExprUtils.simplify*/(Or(facts.getOrDefault(name, False()), And(Eq(a.getRef(), Int(idx1)), Eq(b.getRef(), Int(idx2))))));
		}

		private Decl<FuncType<IntType, FuncType<IntType, BoolType>>> getBinaryRel(final String name) {
			checkArgument(binaryRelations.containsKey(name));
			return binaryRelations.get(name);
		}

		private Decl<FuncType<IntType, BoolType>> getUnaryRel(final String name) {
			checkArgument(unaryRelations.containsKey(name));
			return unaryRelations.get(name);
		}

		private ParamDecl<IntType> getA() {
			return a;
		}

		private ParamDecl<IntType> getB() {
			return b;
		}

		@Override
		public SmtMemoryModelChecker build(List<Tuple2<XcfaLabel, ConstDecl<?>>> dataFlow) {
			for (Tuple2<XcfaLabel, ConstDecl<?>> objects : dataFlow) {
				if(objects.get1() instanceof XcfaLabel.StoreXcfaLabel) {
					for (Tuple2<XcfaLabel, ConstDecl<?>> objects1 : dataFlow) {
						if(objects1.get1() instanceof XcfaLabel.LoadXcfaLabel) {
							final ConstDecl<?> storeVar = objects.get2();
							final ConstDecl<?> loadVar = objects1.get2();
							final XcfaLabel store = objects.get1();
							final XcfaLabel load = objects1.get1();
							final ImplyExpr rf = Imply(App(App(binaryRelations.get("rf").getRef(), Int(factIdxLut.get(store))), Int(factIdxLut.get(load))), Eq(storeVar.getRef(), loadVar.getRef()));
							solver.add(rf);
							System.err.println("Adding assumption: " + rf);
						}
					}
				}
			}
			return new SmtMemoryModelChecker(this);
		}

		@Override
		public void pop() {
			solver.pop();
		}

		@Override
		public void push() {
			solver.push();
		}

		@Override
		public void addReadProgramLoc(Object o, Object o2, Object o3) {
			addUnaryFact("R", o);
			addBinaryFact("intRaw",o, o2);
			addBinaryFact("locRaw", o, o3);
		}

		@Override
		public void addWriteProgramLoc(Object o, Object o2, Object o3) {
			addUnaryFact("W", o);
			addBinaryFact("intRaw",o, o2);
			addBinaryFact("locRaw", o, o3);

		}

		@Override
		public void addFenceLoc(Object o, Object o2) {
			addUnaryFact("F", o);
			addBinaryFact("intRaw",o, o2);
		}

		@Override
		public void addProgramLoc(Object o) {
			addUnaryFact("meta", o);
		}

		@Override
		public void addProgramLoc(Object o, Object o2) {
			addProgramLoc(o);
			addBinaryFact("intRaw", o, o2);
		}

		@Override
		public void addProgramLoc(Object o, Object o2, Object o3) {
			addProgramLoc(o, o2);
			addBinaryFact("locRaw", o, o3);
		}

		@Override
		public void addPoEdge(Object programLocA, Object programLocB) {
			addBinaryFact("poRaw", programLocA, programLocB);
		}

		@Override
		public String createProduct(String newRule, String existingRule1, String existingRule2) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createAlternative(String newRule, String existingRule) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createUnion(String newRule, String existingRule1, String existingRule2) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createIntersection(String newRule, String existingRule1, String existingRule2) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createDifference(String newRule, String existingRule1, String existingRule2) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createInverse(String newRule, String existingRule) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createTransitive(String newRule, String existingRule) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createSelfTransitive(String newRule, String existingRule) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createSuccessor(String newRule, String existingRule1, String existingRule2) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public String createRelation(String newRelation, int arity) {
			throw new UnsupportedOperationException("Not yet implemented");
		}

		@Override
		public void assertIrreflexive(String rule) {

		}

		@Override
		public void assertEmpty(String rule) {

		}

		@Override
		public void assertAcyclic(String rule) {

		}
	}

	private static class EqualityLinkedHashMap<K, V> implements Map<K, V>{
		private final Map<K, Collection<Tuple2<K, Integer>>> buckets;
		private final List<V> heap;

		public EqualityLinkedHashMap() {
			buckets = new LinkedHashMap<>();
			heap = new LinkedList<>();
		}

		public EqualityLinkedHashMap(final EqualityLinkedHashMap<K, V> map) {
			buckets = new LinkedHashMap<>(map.buckets);
			heap = new LinkedList<>(map.heap);
		}

		@Override
		public int size() {
			return heap.size();
		}

		@Override
		public boolean isEmpty() {
			return heap.isEmpty();
		}

		@Override
		public boolean containsKey(Object o) {
			final Collection<Tuple2<K, Integer>> entries = buckets.get(o);
			if(entries != null) {
				for (Tuple2<K, Integer> entry : entries) {
					if (entry.get1() == o) return true;
				}
			}
			return false;
		}

		@Override
		public boolean containsValue(Object o) {
			return heap.contains(o);
		}

		private Integer getIndex(Object o) {
			final Collection<Tuple2<K, Integer>> entries = buckets.get(o);
			if(entries != null) {
				for (Tuple2<K, Integer> entry : entries) {
					if (entry.get1() == o) return entry.get2();
				}
			}
			return null;
		}

		@Override
		public V get(Object o) {
			final Integer index = getIndex(o);
			return index == null ? null : heap.get(index);
		}

		@Override
		public V put(K k, V v) {
			final Integer index = getIndex(k);
			if(index == null) {
				buckets.putIfAbsent(k, new ArrayList<>());
				buckets.get(k).add(Tuple2.of(k, heap.size()));
				heap.add(v);
			} else {
				heap.remove((int)index);
				heap.add(index, v);
			}
			return v;
		}

		@Override
		public V remove(Object o) {
			final Integer index = getIndex(o);
			if(index == null) {
				return null;
			} else {
				final V v = heap.get(index);
				buckets.get(o).remove(Tuple2.of(o, index));
				heap.remove((int)index);
				return v;
			}
		}

		@Override
		public void putAll(Map<? extends K, ? extends V> map) {
			map.forEach(this::put);

		}

		@Override
		public void clear() {
			heap.clear();
			buckets.clear();
		}

		@Override
		public Set<K> keySet() {
			throw new UnsupportedOperationException("Key set is not possible for an EqualityLinkedHashMap!");
		}

		@Override
		public Collection<V> values() {
			return heap;
		}

		@Override
		public Set<Entry<K, V>> entrySet() {
			Set<Entry<K, V>> ret = new LinkedHashSet<>();
			for (Entry<K, Collection<Tuple2<K, Integer>>> entry : buckets.entrySet()) {
				K k = entry.getKey();
				Collection<Tuple2<K, Integer>> tuple2s = entry.getValue();
				for (Tuple2<K, Integer> tuple2 : tuple2s) {
					ret.add(Map.entry(k, heap.get(tuple2.get2())));
				}
			}
			return ret;
		}
	}
}
