package hu.bme.mit.theta.cat.solver;

import com.google.common.base.Supplier;
import com.google.common.collect.Lists;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;
import static com.google.common.collect.Collections2.permutations;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;

public class DatalogMemoryModelChecker implements MemoryModelSolver<Object, Object>{
	private final List<List<Tuple2<Object, Object>>> rf;

	private DatalogMemoryModelChecker(final Builder builder) {
		final Datalog program = builder.program;
		rf = new ArrayList<>();
		chooseRfEdges(builder.validators, program, program.getRelations().get("rf"), builder.reads, builder.writes, rf, new ArrayList<>());
	}

	private boolean chooseCos(final Set<Supplier<Boolean>> validators, final Map<Object, List<Object>> coWrites, final Datalog program, final Datalog.Relation co) {
		if(coWrites.size() == 0) {
			return true;
		}
		final Map.Entry<Object, List<Object>> writeEntry = coWrites.entrySet().stream().findFirst().get();
		final Map<Object, List<Object>> newWrites = new LinkedHashMap<>(coWrites);
		newWrites.remove(writeEntry.getKey());
		if(writeEntry.getValue().size() <= 1) chooseCos(validators, newWrites, program, co);
		else {
			for (List<Object> permutation : permutations(writeEntry.getValue())) {
				program.push();
				for (int i = 0; i < permutation.size() - 1; i++) {
					co.addFact(TupleN.of(GenericDatalogArgument.createArgument(permutation.get(i)), GenericDatalogArgument.createArgument(permutation.get(i + 1))));
				}
				if (validate(validators)) {
					if(chooseCos(validators, newWrites, program, co)) return true;
				}
				program.pop();
			}
		}
		return false;
	}

	private void chooseRfEdges(final Set<Supplier<Boolean>> validators, final Datalog program, final Datalog.Relation rf, final Map<Object, List<Object>> reads, final Map<Object, List<Object>> writes, final List<List<Tuple2<Object, Object>>> ret, final List<Tuple2<Object, Object>> current) {
		if(reads.size() == 0) {
			if(chooseCos(validators, writes, program, program.getRelations().get("co")))
				ret.add(List.copyOf(current));
		} else {
			final Map.Entry<Object, List<Object>> readEntry = reads.entrySet().stream().findFirst().get();
			final Object read = head(readEntry.getValue());
			final List<Object> tail = tail(readEntry.getValue());
			final Map<Object, List<Object>> newReads = new LinkedHashMap<>(reads);
			if(tail.size() == 0) newReads.remove(readEntry.getKey());
			else newReads.put(readEntry.getKey(), tail);
			for (Object write : writes.get(readEntry.getKey())) {
				program.push();
				rf.addFact(TupleN.of(GenericDatalogArgument.createArgument(write), GenericDatalogArgument.createArgument(read)));
				if (validate(validators)) {
					current.add(Tuple2.of(write, read));
					chooseRfEdges(validators, program, rf, newReads, writes, ret, current);
					current.remove(Tuple2.of(write, read));
					program.pop();
				} else {
					program.pop();
				}
			}
		}
	}

	private boolean validate(final Set<Supplier<Boolean>> validators) {
		for (Supplier<Boolean> validator : validators) {
			if(!validator.get()) return false;
		}
		return true;
	}


	@Override
	public Collection<? extends Collection<Tuple2<Object, Object>>> getAllRf() {
		return rf;
	}

	public static Builder builder() {
		return new Builder();
	}

	public static class Builder implements ProgramBuilder<Object, Object, Object> {

		private final Datalog program;
		private final Map<Datalog.Relation, Runnable> postProcessRelations;
		private final Set<Supplier<Boolean>> validators;
		private final Map<Object, List<Object>> reads;
		private final Map<Object, List<Object>> writes;

		private Builder() {
			program = Datalog.createProgram();
			postProcessRelations = new LinkedHashMap<>();
			validators = new LinkedHashSet<>();
			reads = new LinkedHashMap<>();
			writes = new LinkedHashMap<>();

			final Datalog.Relation universe = program.createRelation("U", 1);

			final Datalog.Relation meta = program.createRelation("meta", 1);
			final Datalog.Relation f = program.createRelation("F", 1);
			final Datalog.Relation r = program.createRelation("R", 1);
			final Datalog.Relation w = program.createRelation("W", 1);

			final Datalog.Relation m = program.createRelation("M", 1);

			final Datalog.Relation id = program.createRelation("id", 2);
			final Datalog.Relation po = program.createRelation("po", 2);
			final Datalog.Relation rf = program.createRelation("rf", 2);
			final Datalog.Relation co = program.createRelation("co", 2);
			final Datalog.Relation fr = program.createRelation("fr", 2);
			final Datalog.Relation loc = program.createRelation("loc", 2);
			final Datalog.Relation in = program.createRelation("int", 2);
			final Datalog.Relation ex = program.createRelation("ext", 2);
			final Datalog.Relation amo = program.createRelation("amo", 2);

			postProcessRelations.put(ex, () -> {
				final Collection<TupleN<DatalogArgument>> elements = universe.getElements();
				final Collection<TupleN<DatalogArgument>> intElements = in.getElements();
				for (TupleN<DatalogArgument> elementA : elements) {
					for (TupleN<DatalogArgument> elementB : elements) {
						final TupleN<DatalogArgument> newElement = TupleN.of(elementA.get(0), elementB.get(0));
						if(!intElements.contains(newElement)) ex.addFact(newElement);
					}
				}
			});

			final Datalog.Variable a = program.getVariable();
			final Datalog.Variable b = program.getVariable();
			final Datalog.Variable c = program.getVariable();

			universe.addRule(TupleN.of(a), Set.of(Tuple2.of(r, TupleN.of(a))));
			universe.addRule(TupleN.of(a), Set.of(Tuple2.of(w, TupleN.of(a))));
			universe.addRule(TupleN.of(a), Set.of(Tuple2.of(f, TupleN.of(a))));
			universe.addRule(TupleN.of(a), Set.of(Tuple2.of(meta, TupleN.of(a))));

			m.addRule(TupleN.of(a), Set.of(Tuple2.of(r, TupleN.of(a))));
			m.addRule(TupleN.of(a), Set.of(Tuple2.of(w, TupleN.of(a))));

			po.addRule(TupleN.of(a, b), Set.of(Tuple2.of(po, TupleN.of(a, c)), Tuple2.of(po, TupleN.of(c, b))));
			co.addRule(TupleN.of(a, b), Set.of(Tuple2.of(co, TupleN.of(a, c)), Tuple2.of(co, TupleN.of(c, b))));

			loc.addRule(TupleN.of(a, b), Set.of(Tuple2.of(loc, TupleN.of(a, c)), Tuple2.of(loc, TupleN.of(c, b))));
			loc.addRule(TupleN.of(a, b), Set.of(Tuple2.of(loc, TupleN.of(b, a))));

			in.addRule(TupleN.of(a, b), Set.of(Tuple2.of(in, TupleN.of(a, c)), Tuple2.of(in, TupleN.of(c, b))));
			in.addRule(TupleN.of(a, b), Set.of(Tuple2.of(in, TupleN.of(b, a))));

			amo.addRule(TupleN.of(a, b), Set.of(Tuple2.of(amo, TupleN.of(a, c)), Tuple2.of(amo, TupleN.of(c, b))));
			amo.addRule(TupleN.of(a, b), Set.of(Tuple2.of(amo, TupleN.of(b, a))));

			id.addRule(TupleN.of(a, a), Set.of(Tuple2.of(universe, TupleN.of(a))));

			fr.addRule(TupleN.of(a, b), Set.of(Tuple2.of(rf, TupleN.of(c, a)), Tuple2.of(co, TupleN.of(c, b))));

//			final Datalog.Relation locW = program.createRelation("locW", 2);
//			locW.addRule(TupleN.of(a, b), Set.of(Tuple2.of(loc, TupleN.of(a, b)), Tuple2.of(w, TupleN.of(a)), Tuple2.of(w, TupleN.of(b))));
//
//			assertAcyclic("co");
//			assertIrreflexive("co");
//			final Boolean[] coValidatorHelper = {false};
//			validators.add(() -> {
//				if(coValidatorHelper[0]) return true;
//				coValidatorHelper[0] = true;
//
//				final boolean canChooseCos = chooseCos(writes, program, co);
//
//				coValidatorHelper[0] = false;
//				return canChooseCos;
//			});
		}


		@Override
		public void addReadProgramLoc(Object o, Object o2, Object o3) {
			reads.putIfAbsent(o3, new LinkedList<>());
			reads.get(o3).add(o);
			program.getRelations().get("R").addFact(TupleN.of(GenericDatalogArgument.createArgument(o)));
			program.getRelations().get("int").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o2)));
			program.getRelations().get("loc").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o3)));
		}

		@Override
		public void addWriteProgramLoc(Object o, Object o2, Object o3) {
			writes.putIfAbsent(o3, new LinkedList<>());
			writes.get(o3).add(o);
			program.getRelations().get("W").addFact(TupleN.of(GenericDatalogArgument.createArgument(o)));
			program.getRelations().get("int").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o2)));
			program.getRelations().get("loc").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o3)));

		}

		@Override
		public void addFenceLoc(Object o, Object o2) {
			program.getRelations().get("F").addFact(TupleN.of(GenericDatalogArgument.createArgument(o)));
			program.getRelations().get("int").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o2)));

		}

		@Override
		public void addProgramLoc(Object o) {
			program.getRelations().get("meta").addFact(TupleN.of(GenericDatalogArgument.createArgument(o)));
		}

		@Override
		public void addProgramLoc(Object o, Object o2) {
			addProgramLoc(o);
			program.getRelations().get("int").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o2)));
		}

		@Override
		public void addProgramLoc(Object o, Object o2, Object o3) {
			addProgramLoc(o, o2);
			program.getRelations().get("loc").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o3)));

		}

		@Override
		public void addPoEdge(Object programLocA, Object programLocB) {
			program.getRelations().get("po").addFact(TupleN.of(GenericDatalogArgument.createArgument(programLocA), GenericDatalogArgument.createArgument(programLocB)));
		}

		@Override
		public String createProduct(String newRule, String existingRule1, String existingRule2) {
			checkState(program.getRelations().containsKey(existingRule1), "Relation " + existingRule1 + " does not exist.");
			checkState(program.getRelations().containsKey(existingRule2), "Relation " + existingRule2 + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation1 = program.getRelations().get(existingRule1);
			final Datalog.Relation relation2 = program.getRelations().get(existingRule2);
			List<Datalog.Variable> vars1 = new ArrayList<>();
			List<Datalog.Variable> vars2 = new ArrayList<>();
			List<Datalog.Variable> vars = new ArrayList<>();
			for (int i = 0; i < relation1.getArity(); i++) {
				vars1.add(program.getVariable());
				vars.add(program.getVariable());
			}
			for (int i = 0; i < relation2.getArity(); i++) {
				vars2.add(program.getVariable());
				vars.add(program.getVariable());
			}
			final Datalog.Relation relation = program.createRelation(newRule, relation1.getArity());
			relation.addRule(TupleN.of(vars), Set.of(Tuple2.of(relation1, TupleN.of(vars1)), Tuple2.of(relation2, TupleN.of(vars2))));
			return newRule;
		}

		@Override
		public String createAlternative(String newRule, String existingRule) {
			checkState(program.getRelations().containsKey(existingRule), "Relation " + existingRule + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation = program.getRelations().get(existingRule);
			List<Datalog.Variable> vars = new ArrayList<>();
			for (int i = 0; i < relation.getArity(); i++) {
				vars.add(program.getVariable());
			}
			program.createRelation(newRule, relation.getArity()).addRule(TupleN.of(vars), Set.of(Tuple2.of(relation, TupleN.of(vars))));
			return newRule;
		}

		@Override
		public String createUnion(String newRule, String existingRule1, String existingRule2) {
			checkState(program.getRelations().containsKey(existingRule1) || existingRule1.equals(newRule), "Relation " + existingRule1 + " does not exist.");
			checkState(program.getRelations().containsKey(existingRule2) || existingRule2.equals(newRule), "Relation " + existingRule2 + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation1 = program.getRelations().get(existingRule1);
			final Datalog.Relation relation2 = program.getRelations().get(existingRule2);
			checkState(relation1.getArity() == relation2.getArity(), "Rules {" + existingRule1 + ", " + existingRule2 + "} have different arities!");
			List<Datalog.Variable> vars = new ArrayList<>();
			for (int i = 0; i < relation1.getArity(); i++) {
				vars.add(program.getVariable());
			}
			final Datalog.Relation relation = program.createRelation(newRule, relation1.getArity());
			relation.addRule(TupleN.of(vars), Set.of(Tuple2.of(relation1, TupleN.of(vars))));
			relation.addRule(TupleN.of(vars), Set.of(Tuple2.of(relation2, TupleN.of(vars))));
			return newRule;
		}

		@Override
		public String createIntersection(String newRule, String existingRule1, String existingRule2) {
			checkState(program.getRelations().containsKey(existingRule1) || existingRule1.equals(newRule), "Relation " + existingRule1 + " does not exist.");
			checkState(program.getRelations().containsKey(existingRule2) || existingRule2.equals(newRule), "Relation " + existingRule2 + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation1 = program.getRelations().get(existingRule1);
			final Datalog.Relation relation2 = program.getRelations().get(existingRule2);
			checkState(relation1.getArity() == relation2.getArity(), "Rules {" + existingRule1 + ", " + existingRule2 + "} have different arities!");
			List<Datalog.Variable> vars = new ArrayList<>();
			for (int i = 0; i < relation1.getArity(); i++) {
				vars.add(program.getVariable());
			}
			final Datalog.Relation relation = program.createRelation(newRule, relation1.getArity());
			relation.addRule(TupleN.of(vars), Set.of(Tuple2.of(relation1, TupleN.of(vars)), Tuple2.of(relation2, TupleN.of(vars))));
			return newRule;
		}

		@Override
		public String createDifference(String newRule, String existingRule1, String existingRule2) {
			checkState(program.getRelations().containsKey(existingRule1), "Relation " + existingRule1 + " does not exist.");
			checkState(program.getRelations().containsKey(existingRule2), "Relation " + existingRule2 + " does not exist.");
			checkState(!newRule.equals(existingRule1) && !newRule.equals(existingRule2), "Difference cannot be recursive!");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation1 = program.getRelations().get(existingRule1);
			final Datalog.Relation relation2 = program.getRelations().get(existingRule2);
			checkState(relation1.getArity() == relation2.getArity(), "Rules {" + existingRule1 + ", " + existingRule2 + "} have different arities!");
			final Datalog.Relation relation = program.createRelation(newRule, relation1.getArity());
			postProcessRelations.put(relation, () -> {
				final Collection<TupleN<DatalogArgument>> sub = relation2.getElements();
				for (TupleN<DatalogArgument> element : relation1.getElements()) {
					if(!sub.contains(element)) relation.addFact(element);
				}
			});
			return newRule;
		}

		@Override
		public String createRelation(String newRelation, int arity) {
			checkState(!program.getRelations().containsKey(newRelation), "Relation " + newRelation + " already exists.");
			program.createRelation(newRelation, arity);
			return newRelation;
		}

		@Override
		public String createInverse(String newRule, String existingRule) {
			checkState(program.getRelations().containsKey(existingRule), "Relation " + existingRule + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation = program.getRelations().get(existingRule);
			List<Datalog.Variable> vars = new ArrayList<>();
			for (int i = 0; i < relation.getArity(); i++) {
				vars.add(program.getVariable());
			}
			program.createRelation(newRule, relation.getArity()).addRule(TupleN.of(vars), Set.of(Tuple2.of(relation, TupleN.of(Lists.reverse(vars)))));
			return newRule;
		}

		@Override
		public String createTransitive(String newRule, String existingRule) {
			checkState(program.getRelations().containsKey(existingRule), "Relation " + existingRule + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			program.createTransitive(newRule, program.getRelations().get(existingRule));
			return newRule;
		}

		@Override
		public String createSelfTransitive(String newRule, String existingRule) {
			checkState(program.getRelations().containsKey(existingRule), "Relation " + existingRule + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation = program.getRelations().get(existingRule);
			final Datalog.Relation transitive = program.createTransitive(newRule, relation);
			List<Datalog.Variable> vars = new ArrayList<>();
			final Datalog.Variable var = program.getVariable();
			for (int i = 0; i < relation.getArity(); i++) {
				vars.add(var);
			}
			transitive.addRule(TupleN.of(vars), Set.of(Tuple2.of(program.getRelations().get("U"), TupleN.of(var))));
			return newRule;
		}

		@Override
		public String createSuccessor(String newRule, String existingRule1, String existingRule2) {
			checkState(program.getRelations().containsKey(existingRule1) || existingRule1.equals(newRule), "Relation " + existingRule1 + " does not exist.");
			checkState(program.getRelations().containsKey(existingRule2) || existingRule2.equals(newRule), "Relation " + existingRule2 + " does not exist.");
			checkState(!program.getRelations().containsKey(newRule), "Relation " + newRule + " already exists.");
			final Datalog.Relation relation1 = program.getRelations().get(existingRule1);
			final Datalog.Relation relation2 = program.getRelations().get(existingRule2);
			checkState(relation1.getArity() == relation2.getArity() && relation1.getArity() == 2, "Rules {" + existingRule1 + ", " + existingRule2 + "} have different arities, or are not binary!");
			List<Datalog.Variable> vars = new ArrayList<>();
			for (int i = 0; i < 3; i++) {
				vars.add(program.getVariable());
			}
			final Datalog.Relation relation = program.createRelation(newRule, relation1.getArity());
			relation.addRule(TupleN.of(vars.get(0), vars.get(2)), Set.of(Tuple2.of(relation1, TupleN.of(vars.subList(0, 2))), Tuple2.of(relation2, TupleN.of(vars.subList(1, 3)))));
			return newRule;
		}

		@Override
		public void assertIrreflexive(String rule) {
			final String irreflexive = createDifference("irreflexive_" + rule, "id", rule);
			validators.add(() -> program.getRelations().get(irreflexive).getElements().size() == 0);
		}

		@Override
		public void assertEmpty(String rule) {
			checkState(program.getRelations().containsKey(rule), "Relation " + rule + " does not exist.");
			validators.add(() -> program.getRelations().get(rule).getElements().size() == 0);
		}

		@Override
		public void assertAcyclic(String rule) {
			final String acyclic = createDifference("acyclic_" + rule, "id", createTransitive("acyclic_" + rule + "_tmp", rule));
			validators.add(() -> program.getRelations().get(acyclic).getElements().size() == 0);
		}

		@Override
		public MemoryModelSolver<Object, Object> build(List<Tuple2<XcfaLabel, ConstDecl<?>>> dataFlow) {
			for (Runnable postProcessRelation : postProcessRelations.values()) {
				postProcessRelation.run();
			}
			return new DatalogMemoryModelChecker(this);
		}

		@Override
		public void pop() {
			program.pop();
		}

		@Override
		public void push() {
			program.push();
		}
	}
}
