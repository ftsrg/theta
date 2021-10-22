package hu.bme.mit.theta.cat.solver;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class DatalogOnlyMemoryModelBuilder extends MemoryModelBuilder {
	private final Datalog program;
	private final Collection<Tuple3<Datalog.Relation, Datalog.Relation, Datalog.Relation>> differences; // 1 = 2 \ 3
	private final Collection<String> emptyAssertions;
	private final List<Object> heap;

	private DatalogOnlyMemoryModelBuilder(final MemoryModel memoryModel) {
		super(memoryModel);
		this.program = Datalog.createProgram();
		differences = new ArrayList<>();
		emptyAssertions = new ArrayList<>();
		heap = new ArrayList<>();
		memoryModel.applyRules(this);
		addRule(new RuleDerivation.Intersection("w-loc",
						new RuleDerivation.CartesianProduct("w-cart",
								new RuleDerivation.Element("W", 1),
								new RuleDerivation.Element("W", 1)),
						new RuleDerivation.Element("loc", 2)));
//		addRule(new RuleDerivation.Difference("norf-r",
//						new RuleDerivation.Intersection("norf-r2",
//								new RuleDerivation.CartesianProduct("wr",
//										new RuleDerivation.Element("W", 1),
//										new RuleDerivation.Element("R", 1)),
//								new RuleDerivation.Element("loc", 2)),
//						new RuleDerivation.Element("rf", 2)));
//		assertEmpty("norf-r");
	}

	@Override
	public Collection<Expr<BoolType>> getAssertions() {
		throw new UnsupportedOperationException();
	}

	private DatalogOnlyMemoryModelBuilder(final DatalogOnlyMemoryModelBuilder from){
		super(from);
		this.program = from.program.duplicate();
		this.differences = new ArrayList<>(from.differences);
		this.emptyAssertions = new ArrayList<>(from.emptyAssertions);
		this.heap = new ArrayList<>(from.heap);
	}

	public static DatalogOnlyMemoryModelBuilder create(final MemoryModel memoryModel) {
		return new DatalogOnlyMemoryModelBuilder(memoryModel);
	}

	private void addDifference(final Datalog.Relation goal, final Datalog.Relation A, final Datalog.Relation B) {
		differences.add(Tuple3.of(goal, A, B));
	}

	@Override
	public List<TupleN<?>> get(String rule, Valuation valuation) {
		throw new UnsupportedOperationException();
	}

	@Override
	public List<TupleN<Integer>> getNumbered(String rule, Valuation valuation) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void assertAcyclic(String ruleDerivation) {
		final Datalog.Relation relation = checkNotNull(program.getRelations().get(ruleDerivation));
		final Datalog.Relation transitive = program.createTransitive(ruleDerivation + "_tr", relation);
		final Datalog.Relation cycle = program.createRelation(ruleDerivation + "_cycle", 2);
		Datalog.Variable a = program.getVariable();
		cycle.addRule(TupleN.of(a, a), Set.of(Tuple2.of(transitive, TupleN.of(a, a))));
		emptyAssertions.add(ruleDerivation + "_cycle");
	}

	@Override
	public void assertIrreflexive(String ruleDerivation) {
		final Datalog.Relation relation = checkNotNull(program.getRelations().get(ruleDerivation));
		final Datalog.Relation reflexive = program.createRelation(ruleDerivation + "_reflexive", 2);
		Datalog.Variable a = program.getVariable();
		reflexive.addRule(TupleN.of(a, a), Set.of(Tuple2.of(relation, TupleN.of(a, a))));
		emptyAssertions.add(ruleDerivation + "_reflexive");
	}

	@Override
	public void assertEmpty(String ruleDerivation) {
		emptyAssertions.add(ruleDerivation);
	}

	@Override
	public void addRule(RuleDerivation ruleDerivation) {
		ruleDerivation.accept(RuleAdditionVisitor.instance, this);
	}

	@Override
	public void addFact(String name, TupleN<Integer> fact) {
		final Datalog.Relation relation = checkNotNull(program.getRelations().get(name));
		relation.addFact(TupleN.of(fact.toList().stream().map(GenericDatalogArgument::createArgument).collect(Collectors.toList())));
	}

	@Override
	public int addPrimitive(String name, Object primitive) {
		heap.add(primitive);
		addFact(name, TupleN.of(heap.size() - 1));
		return heap.size() - 1;
	}

	@Override
	public List<?> getPrimitives() {
		return ImmutableList.copyOf(heap);
	}

	@Override
	public void rfConstraints(List<Tuple2<Integer, ConstDecl<?>>> writeConst, List<Tuple2<Integer, ConstDecl<?>>> readConst) {
		throw new UnsupportedOperationException("This is not supported for Datalog!");
	}

	private void addDifferences() {
		for (Tuple3<Datalog.Relation, Datalog.Relation, Datalog.Relation> difference : differences) {
			final Datalog.Relation goal = difference.get1();
			final Datalog.Relation a = difference.get2();
			final Datalog.Relation b = difference.get3();
			final Set<TupleN<DatalogArgument>> bElements = new LinkedHashSet<>(b.getElements());
			for (TupleN<DatalogArgument> element : a.getElements()) {
				if(!bElements.contains(element)) goal.addFact(element);
			}
		}
	}

	@Override
	public MemoryModelBuilder duplicate() {
		return new DatalogOnlyMemoryModelBuilder(this);
	}

	@Override
	public boolean check() {
		if (assertionsFail()) return false;
		return findCos(program.getRelations().get("w-loc"), program.getRelations().get("co"));
	}

	private boolean assertionsFail() {
		program.push();
		addDifferences();
		for (Datalog.Relation emptyAssertion : emptyAssertions.stream().map(s -> program.getRelations().get(s)).collect(Collectors.toList())) {
			if(emptyAssertion.getElements().size() > 0) {
				program.pop();
				return true;
			}
		}
		program.pop();
		return false;
	}

	private boolean findCos(Datalog.Relation wloc, Datalog.Relation co) {
		Optional<TupleN<DatalogArgument>> any;
		if((any = wloc.getElements().stream().filter(objects -> !objects.get(0).equals(objects.get(1)) && !co.getElements().contains(objects) && !co.getElements().contains(TupleN.of(Lists.reverse(objects.toList())))).findAny()).isPresent()) {
			program.push();
			co.addFact(any.get());
			if(!assertionsFail() && findCos(wloc, co)) {
				program.pop();
				return true;
			}
			program.pop();
			program.push();
			co.addFact(TupleN.of((List<DatalogArgument>) Lists.reverse(any.get().toList())));
			boolean ret = !assertionsFail() && findCos(wloc, co);
			program.pop();
			return ret;
		} else {
			return !assertionsFail();
		}
	}

	private static class RuleAdditionVisitor implements RuleDerivationVisitor<DatalogOnlyMemoryModelBuilder, Datalog.Relation> {
		private static final DatalogOnlyMemoryModelBuilder.RuleAdditionVisitor instance = new DatalogOnlyMemoryModelBuilder.RuleAdditionVisitor();

		@Override
		public Datalog.Relation visit(RuleDerivation.Element derivation, DatalogOnlyMemoryModelBuilder param) {
			if(!param.program.getRelations().containsKey(derivation.getRule())) {
				param.program.createRelation(derivation.getRule(), derivation.getArity());
			}
			return param.program.getRelations().get(derivation.getRule());
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Union derivation, DatalogOnlyMemoryModelBuilder param) {
			return param.program.createDisjunction(derivation.getRule(), List.of(derivation.getLhs().accept(this, param), derivation.getRhs().accept(this, param)));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Intersection derivation, DatalogOnlyMemoryModelBuilder param) {
			return param.program.createConjuction(derivation.getRule(), List.of(derivation.getLhs().accept(this, param), derivation.getRhs().accept(this, param)));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Difference derivation, DatalogOnlyMemoryModelBuilder param) {
			if(!param.program.getRelations().containsKey(derivation.getRule())) {
				param.program.createRelation(derivation.getRule(), derivation.getArity());
			}
			final Datalog.Relation relation = checkNotNull(param.program.getRelations().get(derivation.getRule()));
			param.addDifference(relation, derivation.getLhs().accept(this, param), derivation.getRhs().accept(this, param));
			return relation;
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Inverse derivation, DatalogOnlyMemoryModelBuilder param) {
			return param.program.createInverse(derivation.getRule(), derivation.getLhs().accept(this, param));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Transitive derivation, DatalogOnlyMemoryModelBuilder param) {
			return param.program.createTransitive(derivation.getRule(), derivation.getLhs().accept(this, param));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.SelfOrTransitive derivation, DatalogOnlyMemoryModelBuilder param) {
			final Datalog.Relation helper = param.program.createRelation(derivation.getRule() + "_helper1", 2);
			Datalog.Variable var1 = param.program.getVariable(), var2 = param.program.getVariable();
			helper.addRule(
					TupleN.of(
							var1,
							var1
					),
					Set.of(
							Tuple2.of(
									helper,
									TupleN.of(var1, var2)
							)
					));
			return param.program.createDisjunction(derivation.getRule(), List.of(
					helper,
					param.program.createTransitive(derivation.getRule() + "_helper2", derivation.getLhs().accept(this, param))));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Consecutive derivation, DatalogOnlyMemoryModelBuilder param) {
			final Datalog.Relation ret = param.program.createRelation(derivation.getRule(), 2);
			Datalog.Variable var1 = param.program.getVariable(), var2 = param.program.getVariable(), var3 = param.program.getVariable();
			ret.addRule(
					TupleN.of(
							var1,
							var3
					),
					Set.of(
							Tuple2.of(
									derivation.getLhs().accept(this, param),
									TupleN.of(var1, var2)
							),
							Tuple2.of(
									derivation.getRhs().accept(this, param),
									TupleN.of(var2, var3)
							)
					));
			return ret;
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.CartesianProduct derivation, DatalogOnlyMemoryModelBuilder param) {
			final Datalog.Relation ret = param.program.createRelation(derivation.getRule(), 2);
			Datalog.Variable var1 = param.program.getVariable(), var2 = param.program.getVariable();
			ret.addRule(
					TupleN.of(
							var1,
							var2
					),
					Set.of(
							Tuple2.of(
									derivation.getLhs().accept(this, param),
									TupleN.of(var1)
							),
							Tuple2.of(
									derivation.getRhs().accept(this, param),
									TupleN.of(var2)
							)
					));
			return ret;
		}
	}


	public void printGraph() {
		final Map<String, Datalog.Relation> relations = program.getRelations();

		final Datalog.Relation w = relations.get("W");
		final Datalog.Relation r = relations.get("R");
		final Datalog.Relation m = relations.get("meta");
		final Datalog.Relation poRaw = relations.get("poRaw");
		final Datalog.Relation rf = relations.get("rf");

		System.err.println("digraph G{");
		for (TupleN<DatalogArgument> element : m.getElements()) {
			System.err.println(element.get(0) + " [shape=point]");
		}
		for (TupleN<DatalogArgument> element : w.getElements()) {
			System.err.println(element.get(0) + " [label=W]");
		}
		for (TupleN<DatalogArgument> element : r.getElements()) {
			System.err.println(element.get(0) + " [label=R]");
		}

		for (TupleN<DatalogArgument> element : poRaw.getElements()) {
			System.err.println(element.get(0) + " -> " + element.get(1));
		}
		for (TupleN<DatalogArgument> element : rf.getElements()) {
			System.err.println(element.get(0) + " -> " + element.get(1) + " [constraint=false,color=red]");
		}
		System.err.println("}");
	}
}
