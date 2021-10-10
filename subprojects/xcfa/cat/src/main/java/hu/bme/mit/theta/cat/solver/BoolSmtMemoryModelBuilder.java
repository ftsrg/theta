package hu.bme.mit.theta.cat.solver;

import com.google.common.base.Supplier;
import com.google.common.collect.Sets;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;
import java.util.StringJoiner;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;
import static com.google.common.collect.Lists.reverse;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Xor;

public class BoolSmtMemoryModelBuilder extends MemoryModelBuilder{
	private List<Expr<BoolType>> solver;
	private final List<Object> primitives;
	private final Map<Tuple2<String, Integer>, Supplier<Map<TupleN<Integer>, Expr<BoolType>>>> rules;
	private final Map<String, Relation> relations;
	private final List<String> emptyAssertions;

	private BoolSmtMemoryModelBuilder(final MemoryModel memoryModel) {
		super(memoryModel);
		this.solver = new ArrayList<>();
		primitives = new ArrayList<>();
		relations = new LinkedHashMap<>();
		rules = new LinkedHashMap<>();
		emptyAssertions = new ArrayList<>();
		memoryModel.applyRules(this);
	}

	@Override
	public List<TupleN<?>> get(final String rule, final Valuation valuation) {
		final Map<TupleN<Integer>, ConstDecl<BoolType>> elements = relations.get(rule).getElements();
		final List<TupleN<?>> ret = new ArrayList<>();
		elements.forEach((objects, boolTypeConstDecl) -> {
			if(((BoolLitExpr)(valuation.eval(boolTypeConstDecl).orElse(False()))).getValue()) {
				final List<Object> wp = new ArrayList<>();
				for (Object object : objects) {
					wp.add(primitives.get((Integer)object));
				}
				ret.add(TupleN.of(wp));
			}
		});
		return ret;
	}

	@Override
	public List<TupleN<Integer>> getNumbered(final String rule, final Valuation valuation) {
		final Map<TupleN<Integer>, ConstDecl<BoolType>> elements = relations.get(rule).getElements();
		final List<TupleN<Integer>> ret = new ArrayList<>();
		elements.forEach((objects, boolTypeConstDecl) -> {
			if(((BoolLitExpr)(valuation.eval(boolTypeConstDecl).orElse(False()))).getValue()) {
				ret.add(objects);
			}
		});
		return ret;
	}

	@Override
	public void assertAcyclic(final String ruleDerivation) {
		final RuleDerivation.Element element = new RuleDerivation.Element(ruleDerivation, 2);
		addRule(new RuleDerivation.Transitive("acyclic_" + ruleDerivation, element));
		assertIrreflexive("acyclic_" + ruleDerivation);
	}

	@Override
	public void assertIrreflexive(final String ruleDerivation) {
		final RuleDerivation.Element element = new RuleDerivation.Element(ruleDerivation, 2);
		addRule(new RuleDerivation.Intersection("irreflexive_" + ruleDerivation, element, new RuleDerivation.Element("id", 2)));
		assertEmpty("irreflexive_" + ruleDerivation);
	}

	@Override
	public void assertEmpty(final String ruleDerivation) {
		emptyAssertions.add(ruleDerivation);
	}

	public static BoolSmtMemoryModelBuilder create(final MemoryModel memoryModel) {
		return new BoolSmtMemoryModelBuilder(memoryModel);
	}

	@Override
	public void addRule(final RuleDerivation ruleDerivation) {
		String name = ruleDerivation.getRule();
		relations.putIfAbsent(name, new Relation(ruleDerivation.getArity(), name));
		rules.put(Tuple2.of(name, ruleDerivation.getArity()), () -> ruleDerivation.accept(BoolSmtRuleDerivationVisitor.instance, BoolSmtMemoryModelBuilder.this));
	}

	@Override
	public void addFact(final String name, final TupleN<Integer> fact) {
		checkState(fact.arity() > 1, "Primitives (unary facts) can only be added via the addPrimitive function!");
		relations.putIfAbsent(name, new Relation(fact.arity(), name));
		relations.get(name).addFact(fact);
	}

	@Override
	public int addPrimitive(String name, Object primitive) {
		primitives.add(primitive);
		relations.putIfAbsent(name, new Relation(1, name));
		relations.get(name).addFact(TupleN.of(primitives.size() - 1));
		return primitives.size() - 1;
	}

	@Override
	public Expr<BoolType> getRfConstraints(List<Tuple2<Integer, ConstDecl<?>>> writeConst, List<Tuple2<Integer, ConstDecl<?>>> readConst) {
		checkState(relations.containsKey("rf"), "Read-from not defined!");
		final int maxid = primitives.size();
		if(relations.containsKey("id")) {
			final Relation id = relations.get("id");
			for (int i = 0; i < maxid; i++) {
				id.addFact(TupleN.of(i, i));
			}
		}
		relations.forEach((s, relation) -> relation.createElements(maxid, solver));

		for (Map.Entry<Tuple2<String, Integer>, Supplier<Map<TupleN<Integer>, Expr<BoolType>>>> rule : rules.entrySet()) {
			relations.putIfAbsent(rule.getKey().get1(), new Relation(rule.getKey().get2(), rule.getKey().get1()));
			relations.get(rule.getKey().get1()).createElements(maxid, solver);
			final Map<TupleN<Integer>, Expr<BoolType>> exprs = rule.getValue().get();
			final Relation relation = relations.get(rule.getKey().get1());
			final Map<TupleN<Integer>, ConstDecl<BoolType>> elements = relation.getElements();
			elements.forEach((objects, boolTypeConstDecl) -> {
				final EqExpr<?> constraint = Eq(boolTypeConstDecl.getRef(), exprs.get(objects));
				if(!constraint.getLeftOp().equals(constraint.getRightOp())) {
//					System.err.println("Adding constraint " + constraint);
					solver.add(constraint);
				}
			});
		}
		final Map<TupleN<Integer>, ConstDecl<BoolType>> rf = relations.get("rf").getElements();
		final Map<TupleN<Integer>, ConstDecl<BoolType>> co = relations.get("co").getElements();
		final Map<TupleN<Integer>, ConstDecl<BoolType>> loc = relations.get("loc").getElements();
		final Map<TupleN<Integer>, ConstDecl<BoolType>> writes = relations.get("W").getElements();
		final Map<TupleN<Integer>, ConstDecl<BoolType>> reads = relations.get("R").getElements();

//		System.err.println("------------------");

		for (Tuple2<Integer, ConstDecl<?>> objects : readConst) {
			final List<Expr<BoolType>> operands = new ArrayList<>();
			for (int i = 0; i < writeConst.size(); i++) {
				Tuple2<Integer, ConstDecl<?>> constDeclTuple1 = writeConst.get(i);
				final ConstDecl<BoolType> rfAB1 = rf.get(TupleN.of(constDeclTuple1.get1(), objects.get1()));
				final Expr<BoolType> constraint = Imply(Not(loc.get(TupleN.of(constDeclTuple1.get1(), objects.get1())).getRef()), Not(rfAB1.getRef()));
//				System.err.println("Adding constraint " + constraint);
				solver.add(constraint);
				for (int j = i + 1, writeConstSize = writeConst.size(); j < writeConstSize; j++) {
					Tuple2<Integer, ConstDecl<?>> constDeclTuple2 = writeConst.get(j);
					final ConstDecl<BoolType> rfAB2 = rf.get(TupleN.of(constDeclTuple2.get1(), objects.get1()));
					final Expr<BoolType> implConstraint = Imply(
							And(
									loc.get(TupleN.of(constDeclTuple1.get1(), objects.get1())).getRef(),
									loc.get(TupleN.of(constDeclTuple2.get1(), objects.get1())).getRef()), Not(And(rfAB1.getRef(), rfAB2.getRef())));
//					System.err.println("Adding constraint " + implConstraint);

					solver.add(implConstraint);
				}
				operands.add(And(loc.get(TupleN.of(constDeclTuple1.get1(), objects.get1())).getRef(), rfAB1.getRef()));
			}
			final Expr<BoolType> constraint = Or(operands);
//			System.err.println("Adding constraint " + constraint);
			solver.add(constraint);
		}

//		System.err.println("------------------");


		for (Map.Entry<TupleN<Integer>, ConstDecl<BoolType>> entry : rf.entrySet()) {
			final TupleN<Integer> key = entry.getKey();
			final Integer key1 = key.get(0);
			final Integer key2 = key.get(1);
			final Expr<BoolType> constraint = Imply(Not(And(writes.get(TupleN.of(key1)).getRef(), reads.get(TupleN.of(key2)).getRef())), Not(entry.getValue().getRef()));
//			System.err.println("Adding constraint " + constraint);
			solver.add(constraint);
		}

//		System.err.println("------------------");

		for (Map.Entry<TupleN<Integer>, ConstDecl<BoolType>> entry : co.entrySet()) {
			final TupleN<Integer> key = entry.getKey();
			final Integer key1 = key.get(0);
			final Integer key2 = key.get(1);
			if(!key1.equals(key2)) {
				final TupleN<Integer> reverseKey = TupleN.of(key2, key1);
				final ConstDecl<BoolType> one = entry.getValue();
				final ConstDecl<BoolType> other = co.get(reverseKey);
				final ConstDecl<BoolType> locVar = loc.get(key);
				final Expr<BoolType> constraint0 = Imply(And(locVar.getRef(), And(writes.get(TupleN.of(key1)).getRef(), writes.get(TupleN.of(key2)).getRef())), Xor(one.getRef(), other.getRef()));
				final Expr<BoolType> constraint1 = Imply(Not(And(writes.get(TupleN.of(key1)).getRef(), writes.get(TupleN.of(key2)).getRef())), Not(one.getRef()));
//				System.err.println("Adding constraint " + constraint0);
//				System.err.println("Adding constraint " + constraint1);
				solver.add(constraint0);
				solver.add(constraint1);
			}
			else {
				final Expr<BoolType> constraint = Not(entry.getValue().getRef());
//				System.err.println("Adding constraint " + constraint);
				solver.add(constraint);
			}
		}

//		System.err.println("------------------");

		for (Tuple2<Integer, ConstDecl<?>> objects : writeConst) {
			for (Tuple2<Integer, ConstDecl<?>> objects1 : readConst) {
				final Expr<BoolType> constraint = Imply(rf.get(TupleN.of(objects.get1(), objects1.get1())).getRef(), Eq(objects.get2().getRef(), objects1.get2().getRef()));
//				System.err.println("Adding constraint " + constraint);
				solver.add(constraint);
			}
		}

//		System.err.println("------------------");

		for (String emptyAssertion : emptyAssertions) {
			final Map<TupleN<Integer>, ConstDecl<BoolType>> elements = relations.get(emptyAssertion).getElements();
			final Expr<BoolType> constraint = Not(Or(elements.values().stream().map(Decl::getRef).collect(Collectors.toList())));
//			System.err.println("Adding constraint " + constraint);
			solver.add(constraint);
		}

		return And(solver);
	}

	@Override
	public MemoryModelBuilder duplicate() {
		return this;
	}

	private static class BoolSmtRuleDerivationVisitor implements RuleDerivationVisitor<BoolSmtMemoryModelBuilder, Map<TupleN<Integer>, Expr<BoolType>>> {
		private static int rulecounter = 0;
		private static final BoolSmtRuleDerivationVisitor instance = new BoolSmtRuleDerivationVisitor();

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.Element derivation, BoolSmtMemoryModelBuilder param) {
			final String rule = derivation.getRule();
			if(!param.relations.containsKey(rule)) {
				param.relations.put(rule, new Relation(derivation.getArity(), derivation.getRule()));
				param.relations.get(rule).createElements(param.primitives.size(), null);
			}
			return param.relations.get(rule).getElements().entrySet().stream().map(e -> Map.entry(e.getKey(), e.getValue().getRef())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.Union derivation, BoolSmtMemoryModelBuilder param) {
			final Map<TupleN<Integer>, Expr<BoolType>> lhs = derivation.getLhs().accept(this, param);
			final Map<TupleN<Integer>, Expr<BoolType>> rhs = derivation.getRhs().accept(this, param);
			return lhs.entrySet().stream().map(e -> Map.entry(e.getKey(), Or(e.getValue(), rhs.get(e.getKey())))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.Intersection derivation, BoolSmtMemoryModelBuilder param) {
			final Map<TupleN<Integer>, Expr<BoolType>> lhs = derivation.getLhs().accept(this, param);
			final Map<TupleN<Integer>, Expr<BoolType>> rhs = derivation.getRhs().accept(this, param);
			return lhs.entrySet().stream().map(e -> Map.entry(e.getKey(), And(e.getValue(), rhs.get(e.getKey())))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.Difference derivation, BoolSmtMemoryModelBuilder param) {
			final Map<TupleN<Integer>, Expr<BoolType>> lhs = derivation.getLhs().accept(this, param);
			final Map<TupleN<Integer>, Expr<BoolType>> rhs = derivation.getRhs().accept(this, param);
			return lhs.entrySet().stream().map(e -> Map.entry(e.getKey(), And(e.getValue(), Not(rhs.get(e.getKey()))))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.Inverse derivation, BoolSmtMemoryModelBuilder param) {
			final Map<TupleN<Integer>, Expr<BoolType>> lhs = derivation.getLhs().accept(this, param);
			return lhs.keySet().stream().map(boolTypeExpr -> Map.entry(boolTypeExpr, lhs.get(TupleN.of(reverse(boolTypeExpr.toList()))))).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.Transitive derivation, BoolSmtMemoryModelBuilder param) {
			return new RuleDerivation.Union("rule" + rulecounter++,
					derivation.getLhs(),
					new RuleDerivation.Consecutive("rule" + rulecounter++,
							derivation.getLhs(),
							new RuleDerivation.Element(derivation.getRule(), derivation.getArity()))).accept(this, param);
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.SelfOrTransitive derivation, BoolSmtMemoryModelBuilder param) {
			return new RuleDerivation.Union("rule" + rulecounter++, new RuleDerivation.Element("id", 2), new RuleDerivation.Transitive("rule" + rulecounter++, derivation.getLhs())).accept(this, param);
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.Consecutive derivation, BoolSmtMemoryModelBuilder param) {
			final Map<TupleN<Integer>, Expr<BoolType>> lhs = derivation.getLhs().accept(this, param);
			final Map<TupleN<Integer>, Expr<BoolType>> rhs = derivation.getRhs().accept(this, param);

			checkState(derivation.getArity() == 2, "Consecutive derivation is only valid for binary rules!");
			final int size = (int) Math.round(Math.sqrt(rhs.keySet().size()));

			final Map<TupleN<Integer>, Expr<BoolType>> ret = new LinkedHashMap<>();
			for (Map.Entry<TupleN<Integer>, Expr<BoolType>> entry : lhs.entrySet()) {
				final Integer i1 = entry.getKey().get(0);
				final Integer i2 = entry.getKey().get(1);
				Expr<BoolType> boolTypeExpr = entry.getValue();
				for (int i = 0; i < size; i++) {
					final Expr<BoolType> boolTypeExpr1 = rhs.get(TupleN.of(i2, i));
					final TupleN<Integer> tuple = TupleN.of(i1, i);
					ret.put(tuple, Or(ret.getOrDefault(tuple, False()), And(boolTypeExpr, boolTypeExpr1)));
				}
			}
			return ret;
		}

		@Override
		public Map<TupleN<Integer>, Expr<BoolType>> visit(RuleDerivation.CartesianProduct derivation, BoolSmtMemoryModelBuilder param) {
			final Map<TupleN<Integer>, Expr<BoolType>> lhs = derivation.getLhs().accept(this, param);
			final Map<TupleN<Integer>, Expr<BoolType>> rhs = derivation.getRhs().accept(this, param);
			checkState(derivation.getArity() == 2, "Cartesian product is only valid for unary rules!");

			final Map<TupleN<Integer>, Expr<BoolType>> ret = new LinkedHashMap<>();
			for (Map.Entry<TupleN<Integer>, Expr<BoolType>> entry : lhs.entrySet()) {
				TupleN<Integer> objects = entry.getKey();
				Expr<BoolType> boolTypeExpr = entry.getValue();
				for (Map.Entry<TupleN<Integer>, Expr<BoolType>> e : rhs.entrySet()) {
					TupleN<Integer> objects1 = e.getKey();
					Expr<BoolType> boolTypeExpr1 = e.getValue();
					ret.put(TupleN.of(objects.get(0), objects1.get(0)), And(boolTypeExpr1, boolTypeExpr));
				}
			}
			return ret;
		}
	}

	private static class Relation {
		private static final Set<String> groundRelations = Set.of("poRaw", "locRaw", "intRaw", "amoRaw", "id", "W", "R", "F", "meta");
		private final int arity;
		private final String name;
		private int counter = 0;
		private final Map<TupleN<Integer>, ConstDecl<BoolType>> elements;
		private final Optional<Set<TupleN<Integer>>> knownTruths;

		private Relation(int arity, String name) {
			this.arity = arity;
			this.name = name;
			elements = new LinkedHashMap<>();
			knownTruths = groundRelations.contains(name) ? Optional.of(new LinkedHashSet<>()) : Optional.empty();
		}

		private void addFact(TupleN<Integer> fact) {
			checkState(knownTruths.isPresent(), "Only ground relations shall have associated facts!");
			knownTruths.get().add(fact);
		}

		private void createElements(final int maxId, List<Expr<BoolType>> solver) {
			if(elements.size() != 0) return;
			final List<TupleN<Integer>> lists = createLists(new ArrayList<>(), new Stack<>(), arity, maxId);
			for (TupleN<Integer> list : lists) {
				final StringJoiner stringJoiner = new StringJoiner(", ");
				list.forEach(o -> stringJoiner.add(Integer.toString((Integer)o)));
				elements.put(list, Const(name + "(" + stringJoiner + ")", BoolType.getInstance()));
			}
			if(knownTruths.isPresent()) {
				for (TupleN<Integer> objects : Sets.difference(elements.keySet(), knownTruths.get())) {
					// false
//					System.err.println("Adding fact Not(" + elements.get(objects).getRef() + ")");
					solver.add(Not(elements.get(objects).getRef()));
				}
				for (TupleN<Integer> objects : knownTruths.get()) {
					// true
//					System.err.println("Adding fact " + elements.get(objects).getRef());
					solver.add(elements.get(objects).getRef());
				}
			}
		}

		public Map<TupleN<Integer>, ConstDecl<BoolType>> getElements() {
			return elements;
		}

		private List<TupleN<Integer>> createLists(final List<TupleN<Integer>> lists, final Stack<Integer> current, final int toGo, final int maxId) {
			if(toGo == 0) {
				lists.add(TupleN.of(current));
			} else {
				for (int i = 0; i < maxId; i++) {
					current.push(i);
					createLists(lists, current, toGo - 1, maxId);
					current.pop();
				}
			}
			return lists;
		}
	}
}
