package hu.bme.mit.theta.cat.solver;

import hu.bme.mit.theta.common.Tuple2;
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
import java.util.Set;
import java.util.stream.Collectors;

public class BoolDatalogMemoryModelBuilder extends MemoryModelBuilder{
	private final BoolSmtMemoryModelBuilder memoryModelBuilder;
	private final Datalog datalog;
	private final Collection<String> toKeep;

	private BoolDatalogMemoryModelBuilder(MemoryModel memoryModel) {
		super(memoryModel);
		this.memoryModelBuilder = BoolSmtMemoryModelBuilder.create(null);
		this.datalog = Datalog.createProgram();
		toKeep = new LinkedHashSet<>(Set.of("rf", "id", "loc", "co", "po", "amo", "int", "ext"));
		memoryModel.applyRules(this);
	}

	public static BoolDatalogMemoryModelBuilder create(MemoryModel memoryModel) {
		return new BoolDatalogMemoryModelBuilder(memoryModel);
	}

	@Override
	public List<TupleN<?>> get(String rule, Valuation valuation) {
		return memoryModelBuilder.get(rule, valuation);
	}

	@Override
	public List<TupleN<Integer>> getNumbered(String rule, Valuation valuation) {
		return memoryModelBuilder.getNumbered(rule, valuation);
	}

	@Override
	public void assertAcyclic(String ruleDerivation) {
		toKeep.add(ruleDerivation);
		memoryModelBuilder.assertAcyclic(ruleDerivation);
	}

	@Override
	public void assertIrreflexive(String ruleDerivation) {
		toKeep.add(ruleDerivation);
		memoryModelBuilder.assertIrreflexive(ruleDerivation);
	}

	@Override
	public void assertEmpty(String ruleDerivation) {
		toKeep.add(ruleDerivation);
		memoryModelBuilder.assertEmpty(ruleDerivation);
	}

	@Override
	public void addRule(RuleDerivation ruleDerivation) {
		if(!datalog.getRelations().containsKey(ruleDerivation.getRule()))
			datalog.createRelation(ruleDerivation.getRule(), ruleDerivation.getArity());
		List<String> toKeep = new ArrayList<>();
		if(ruleDerivation.accept(IsNotMonotoneVisitor.instance, toKeep)) {
			this.toKeep.addAll(toKeep);
			this.toKeep.add(ruleDerivation.getRule());
			memoryModelBuilder.addRule(ruleDerivation);
		}
		else {
			ruleDerivation.accept(RuleAdditionVisitor.instance, datalog);
		}
	}

	@Override
	public void addFact(String name, TupleN<Integer> fact) {
		if(!datalog.getRelations().containsKey(name))
			datalog.createRelation(name, fact.arity());
		datalog.getRelations().get(name).addFact(TupleN.of(fact.toList().stream().map(GenericDatalogArgument::createArgument).collect(Collectors.toList())));
		if(toKeep.contains(name) || memoryModelBuilder.getRelations().containsKey(name)) {
			memoryModelBuilder.addFact(name, fact);
		}
	}

	@Override
	public int addPrimitive(String name, Object primitive) {
		return memoryModelBuilder.addPrimitive(name, primitive);
	}

	@Override
	public Expr<BoolType> getRfConstraints(List<Tuple2<Integer, ConstDecl<?>>> writeConst, List<Tuple2<Integer, ConstDecl<?>>> readConst) {
		for (String s : toKeep) {
			final Datalog.Relation relation = datalog.getRelations().get(s);
			memoryModelBuilder.addRule(new RuleDerivation.Element(s, relation.getArity()));
			for (TupleN<DatalogArgument> element : relation.getElements()) {
				final TupleN<Integer> tup = TupleN.of(element.toList().stream().map(o -> ((GenericDatalogArgument<Integer>) o).getContent()).collect(Collectors.toList()));
				memoryModelBuilder.addFact(s, tup);
			}
		}
		return memoryModelBuilder.getRfConstraints(writeConst, readConst);
	}

	@Override
	public MemoryModelBuilder duplicate() {
		return null;
	}

	private static class IsNotMonotoneVisitor implements RuleDerivationVisitor<List<String>, Boolean> {
		private static final IsNotMonotoneVisitor instance = new IsNotMonotoneVisitor();

		@Override
		public Boolean visit(RuleDerivation.Element derivation, List<String> param) {
			param.add(derivation.getRule());
			return false;
		}

		@Override
		public Boolean visit(RuleDerivation.Union derivation, List<String> param) {
			return derivation.getLhs().accept(this, param) || derivation.getRhs().accept(this, param);
		}

		@Override
		public Boolean visit(RuleDerivation.Intersection derivation, List<String> param) {
			return derivation.getLhs().accept(this, param) || derivation.getRhs().accept(this, param);
		}

		@Override
		public Boolean visit(RuleDerivation.Difference derivation, List<String> param) {
			return true;
		}

		@Override
		public Boolean visit(RuleDerivation.Inverse derivation, List<String> param) {
			return derivation.getLhs().accept(this, param);
		}

		@Override
		public Boolean visit(RuleDerivation.Transitive derivation, List<String> param) {
			return derivation.getLhs().accept(this, param);
		}

		@Override
		public Boolean visit(RuleDerivation.SelfOrTransitive derivation, List<String> param) {
			return derivation.getLhs().accept(this, param);
		}

		@Override
		public Boolean visit(RuleDerivation.Consecutive derivation, List<String> param) {
			return derivation.getLhs().accept(this, param) || derivation.getRhs().accept(this, param);
		}

		@Override
		public Boolean visit(RuleDerivation.CartesianProduct derivation, List<String> param) {
			return derivation.getLhs().accept(this, param) || derivation.getRhs().accept(this, param);
		}
	}
	private static class RuleAdditionVisitor implements RuleDerivationVisitor<Datalog, Datalog.Relation> {
		private static final RuleAdditionVisitor instance = new RuleAdditionVisitor();

		@Override
		public Datalog.Relation visit(RuleDerivation.Element derivation, Datalog param) {
			if(!param.getRelations().containsKey(derivation.getRule())) {
				param.createRelation(derivation.getRule(), derivation.getArity());
			}
			return param.getRelations().get(derivation.getRule());
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Union derivation, Datalog param) {
			return param.createDisjunction(derivation.getRule(), List.of(derivation.getLhs().accept(this, param), derivation.getRhs().accept(this, param)));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Intersection derivation, Datalog param) {
			return param.createConjuction(derivation.getRule(), List.of(derivation.getLhs().accept(this, param), derivation.getRhs().accept(this, param)));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Difference derivation, Datalog param) {
			throw new UnsupportedOperationException("Cannot apply difference as a datalog relation!");
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Inverse derivation, Datalog param) {
			return param.createInverse(derivation.getRule(), derivation.getLhs().accept(this, param));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Transitive derivation, Datalog param) {
			return param.createTransitive(derivation.getRule(), derivation.getLhs().accept(this, param));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.SelfOrTransitive derivation, Datalog param) {
			final Datalog.Relation helper = param.createRelation(derivation.getRule() + "_helper1", 2);
			Datalog.Variable var1 = param.getVariable(), var2 = param.getVariable();
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
			return param.createDisjunction(derivation.getRule(), List.of(
					helper,
					param.createTransitive(derivation.getRule() + "_helper2", derivation.getLhs().accept(this, param))));
		}

		@Override
		public Datalog.Relation visit(RuleDerivation.Consecutive derivation, Datalog param) {
			final Datalog.Relation ret = param.createRelation(derivation.getRule(), 2);
			Datalog.Variable var1 = param.getVariable(), var2 = param.getVariable(), var3 = param.getVariable();
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
		public Datalog.Relation visit(RuleDerivation.CartesianProduct derivation, Datalog param) {
			final Datalog.Relation ret = param.createRelation(derivation.getRule(), 2);
			Datalog.Variable var1 = param.getVariable(), var2 = param.getVariable();
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
}
