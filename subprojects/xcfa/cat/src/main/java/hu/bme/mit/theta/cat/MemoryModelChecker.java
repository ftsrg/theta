package hu.bme.mit.theta.cat;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.functype.FuncExprs;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class MemoryModelChecker {
	private static final FuncType<IntType, BoolType> unaryPredicate  = FuncExprs.Func(Int(), Bool());
	private static final FuncType<IntType, FuncType<IntType, BoolType>> binaryPredicate = FuncExprs.Func(Int(), FuncExprs.Func(Int(), Bool()));

	private final List<List<Tuple2<Object, Object>>> rf;
	private MemoryModelChecker(final Builder builder) {
		this.rf = new ArrayList<>();

		final ParamDecl<IntType> a = builder.a;
		final ParamDecl<IntType> b = builder.b;
		final Solver solver = Z3SolverFactory.getInstance().createSolver();

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
			solver.add(/*ExprUtils.simplify*/(Forall(List.of(a, b), assumption.withCond(binaryRange))));
			solver.check();
			if(solver.getStatus().isUnsat()) {
				break;
			}
		}
		for (IteExpr<BoolType> assumption : builder.unaryAssumptions) {
			solver.add(/*ExprUtils.simplify*/(Forall(List.of(a), assumption.withCond(unaryRange))));
			solver.check();
			if(solver.getStatus().isUnsat()) {
				break;
			}
		}

		for (Expr<BoolType> nullaryAssumption : builder.nullaryAssumptions) {
			solver.add(/*ExprUtils.simplify*/(nullaryAssumption));
			solver.check();
			if(solver.getStatus().isUnsat()) {
				break;
			}
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
			solver.add(/*ExprUtils.simplify*/(assumption));
			solver.check();
			if(solver.getStatus().isUnsat()) {
				break;
			}
		}

		while(solver.getStatus().isSat()) {
			final Map<Decl<?>, LitExpr<?>> valuation = solver.getModel().toMap();
			final List<Tuple2<Object, Object>> currentRf = new ArrayList<>();
			Expr<BoolType> ref = True();
			for (Map.Entry<Tuple2<Decl<IntType>, Object>, Integer> entry : builder.reads.entrySet()) {
				Tuple2<Decl<IntType>, Object> objects = entry.getKey();
				final Object read = objects.get2();
				final IntLitExpr value = (IntLitExpr) cast(valuation.get(objects.get1()), Int());
				final int idx = (int) value.getValue().longValue();
				final Object write = builder.idxFactLut.get(idx);
				currentRf.add(Tuple2.of(write, read));
				ref = And(ref, Eq(objects.get1().getRef(), value));
			}
			rf.add(currentRf);
			solver.add(Not(ref));
		}
	}

	public void printRf() {
		for (List<Tuple2<Object, Object>> objectObjectMap : rf) {
			for (Tuple2<Object, Object> entry : objectObjectMap) {
				Object o = entry.get1();
				Object o2 = entry.get2();
				System.out.println("rf(" + o + ", " + o2 + ")");
			}
		}
	}

	public static Builder builder() {
		return new Builder();
	}

	public static class Builder {
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

		private Builder() {
			binaryAssumptions = new ArrayList<>();
			unaryAssumptions = new ArrayList<>();
			nullaryAssumptions  = new ArrayList<>();
			reads = new LinkedHashMap<>();
			writes = new LinkedHashMap<>();
			factIdxLut = new LinkedHashMap<>();
			idxFactLut = new LinkedHashMap<>();
			facts = new LinkedHashMap<>();
			binaryRelations = new LinkedHashMap<>();
			unaryRelations  = new LinkedHashMap<>();

			a = Param("a", Int());
			b = Param("b", Int());

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

			// co constraint (special case, itreflexivity and location-specific total order)
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

		public Decl<FuncType<IntType, FuncType<IntType, BoolType>>> createBinaryRelation(final String name) {
			final ConstDecl<FuncType<IntType, FuncType<IntType, BoolType>>> rel = Const(name, binaryPredicate);
			binaryRelations.put(name, rel);
			return rel;
		}

		public Decl<FuncType<IntType, BoolType>> createUnaryPredicate(final String name) {
			final ConstDecl<FuncType<IntType, BoolType>> rel = Const(name, unaryPredicate);
			unaryRelations.put(name, rel);
			return rel;
		}

		public void createBinaryRule(final Decl<FuncType<IntType, FuncType<IntType, BoolType>>> rel, final Expr<BoolType> rule) {
			binaryAssumptions.add(Ite(True(), Eq(App(App(rel.getRef(), a.getRef()), b.getRef()), /*ExprUtils.simplify*/(rule)), Not(App(App(rel.getRef(), a.getRef()), b.getRef()))));
		}

		public void createUnaryRule(final Decl<FuncType<IntType, BoolType>> rel, final Expr<BoolType> rule) {
			unaryAssumptions.add(Ite(True(), Eq(App(rel.getRef(), a.getRef()), /*ExprUtils.simplify*/(rule)), Not(App(rel.getRef(), a.getRef()))));
		}

		public void createBinaryAssumption(final Expr<BoolType> inRange, final Expr<BoolType> notInRange) {
			binaryAssumptions.add(/*ExprUtils.simplify*/Ite(True(), inRange, notInRange));
		}

		public void createUnaryAssumption(final Expr<BoolType> inRange, final Expr<BoolType> notInRange) {
			unaryAssumptions.add(/*ExprUtils.simplify*/Ite(True(), inRange, notInRange));
		}

		public int addUnaryFact(final String name, final Object object) {
			checkArgument(!factIdxLut.containsKey(object), "Object " + object + " is already a fact!");
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

		public void addBinaryFact(final String name, final Object obj1, final Object obj2) {
			checkArgument(factIdxLut.containsKey(obj1) && factIdxLut.containsKey(obj2), "Facts of a relation have to be added manually!");
			final int idx1 = factIdxLut.get(obj1);
			final int idx2 = factIdxLut.get(obj2);
			facts.put(name, /*ExprUtils.simplify*/(Or(facts.getOrDefault(name, False()), And(Eq(a.getRef(), Int(idx1)), Eq(b.getRef(), Int(idx2))))));
		}

		public Decl<FuncType<IntType, FuncType<IntType, BoolType>>> getBinaryRel(final String name) {
			checkArgument(binaryRelations.containsKey(name));
			return binaryRelations.get(name);
		}

		public Decl<FuncType<IntType, BoolType>> getUnaryRel(final String name) {
			checkArgument(unaryRelations.containsKey(name));
			return unaryRelations.get(name);
		}

		public ParamDecl<IntType> getA() {
			return a;
		}

		public ParamDecl<IntType> getB() {
			return b;
		}

		public MemoryModelChecker build() {
			for (Map.Entry<Tuple2<Decl<IntType>, Object>, Integer> entry : reads.entrySet()) {
				final Tuple2<Decl<IntType>, Object> read = entry.getKey();
				final Integer idx = entry.getValue();
				nullaryAssumptions.add(App(App(getBinaryRel("rf").getRef(), read.get1().getRef()), Int(idx)));
			}
			return new MemoryModelChecker(this);
		}

	}
}
