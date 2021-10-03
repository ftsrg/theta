package hu.bme.mit.theta.cat.solver;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.TupleN;
import hu.bme.mit.theta.common.datalog.Datalog;
import hu.bme.mit.theta.common.datalog.DatalogArgument;
import hu.bme.mit.theta.common.datalog.GenericDatalogArgument;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;

public class DatalogMemoryModelChecker implements MemoryModelSolver<Object, Object>{
	private final List<List<Tuple2<Object, Object>>> rf;

	private DatalogMemoryModelChecker(final Builder builder) {
		final Datalog program = builder.program;
		rf = chooseRfEdges(builder.validators, program, program.getRelations().get("rf"), builder.reads, builder.writes, new ArrayList<>(), new ArrayList<>());
	}

	private List<List<Tuple2<Object, Object>>> chooseRfEdges(final Set<Datalog.Relation> validators, final Datalog program, final Datalog.Relation rf, final Set<Object> reads, final Set<Object> writes, final List<List<Tuple2<Object, Object>>> ret, final List<Tuple2<Object, Object>> current) {
		if(reads.size() == 0) {
			ret.add(List.copyOf(current));
		} else {
			final Object read = head(reads);
			for (Object write : writes) {
				program.push();
				rf.addFact(TupleN.of(GenericDatalogArgument.createArgument(write), GenericDatalogArgument.createArgument(read)));
				if (validate(validators)) {
					current.add(Tuple2.of(write, read));
					chooseRfEdges(validators, program, rf, tail(reads), writes, ret, current);
					current.remove(Tuple2.of(write, read));
					program.pop();
				} else {
					program.pop();
				}
			}
		}
		return ret;
	}

	private boolean validate(final Set<Datalog.Relation> validators) {
		for (Datalog.Relation validator : validators) {
			if(validator.getElements().size() > 0) return false;
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
		private final Set<Datalog.Relation> postProcessRelations;
		private final Set<Datalog.Relation> validators;
		private final Set<Object> reads;
		private final Set<Object> writes;

		private Builder() {
			program = Datalog.createProgram();
			postProcessRelations = new LinkedHashSet<>();
			validators = new LinkedHashSet<>();
			reads = new LinkedHashSet<>();
			writes = new LinkedHashSet<>();

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
			final Datalog.Relation ex = program.createRelation("ext", 2);		postProcessRelations.add(ex);
			final Datalog.Relation amo = program.createRelation("amo", 2);

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

			loc.addRule(TupleN.of(a, b), Set.of(Tuple2.of(loc, TupleN.of(a, c)), Tuple2.of(loc, TupleN.of(c, b))));
			loc.addRule(TupleN.of(a, b), Set.of(Tuple2.of(loc, TupleN.of(b, a))));

			in.addRule(TupleN.of(a, b), Set.of(Tuple2.of(in, TupleN.of(a, c)), Tuple2.of(in, TupleN.of(c, b))));
			in.addRule(TupleN.of(a, b), Set.of(Tuple2.of(in, TupleN.of(b, a))));

			amo.addRule(TupleN.of(a, b), Set.of(Tuple2.of(amo, TupleN.of(a, c)), Tuple2.of(amo, TupleN.of(c, b))));
			amo.addRule(TupleN.of(a, b), Set.of(Tuple2.of(amo, TupleN.of(b, a))));

			id.addRule(TupleN.of(a, a), Set.of(Tuple2.of(universe, TupleN.of(a))));

			fr.addRule(TupleN.of(a, b), Set.of(Tuple2.of(rf, TupleN.of(c, a)), Tuple2.of(co, TupleN.of(c, b))));
		}

		@Override
		public void addReadProgramLoc(Object o, Object o2, Object o3) {
			reads.add(o);
			program.getRelations().get("R").addFact(TupleN.of(GenericDatalogArgument.createArgument(o)));
			program.getRelations().get("int").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o2)));
			program.getRelations().get("loc").addFact(TupleN.of(GenericDatalogArgument.createArgument(o), GenericDatalogArgument.createArgument(o3)));
		}

		@Override
		public void addWriteProgramLoc(Object o, Object o2, Object o3) {
			writes.add(o);
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
		public MemoryModelSolver<Object, Object> build() {
			final Map<String, Datalog.Relation> relations = program.getRelations();

			final Datalog.Relation universe = relations.get("U");
			final Datalog.Relation in = relations.get("int");
			final Datalog.Relation ex = relations.get("ext");

			final Collection<TupleN<DatalogArgument>> elements = universe.getElements();
			final Collection<TupleN<DatalogArgument>> intElements = in.getElements();
			for (TupleN<DatalogArgument> elementA : elements) {
				for (TupleN<DatalogArgument> elementB : elements) {
					final TupleN<DatalogArgument> newElement = TupleN.of(elementA.get(0), elementB.get(0));
					if(!intElements.contains(newElement)) ex.addFact(newElement);
				}
			}

			return new DatalogMemoryModelChecker(this);
		}
	}
}
