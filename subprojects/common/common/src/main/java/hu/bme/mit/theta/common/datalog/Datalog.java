package hu.bme.mit.theta.common.datalog;

/*
 * Datalog engine using naive (enumerative) evaluation.
 * Limitations:
 *  - Only relations are supported right now, simple atoms are not
 *  - There is a performance penalty for specific rulesets, see
 *    http://pages.cs.wisc.edu/~paris/cs838-s16/lecture-notes/lecture8.pdf
 */

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;
import hu.bme.mit.theta.common.TupleN;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class Datalog {
	private final Map<String, Relation> relations;
	private boolean debug = false;
	private int stackDepth = 0;

	protected Datalog() {
		relations = new LinkedHashMap<>();
	}

	public static Datalog createProgram() {
		return new Datalog();
	}

	public Map<String, Relation> getRelations() {
		return relations;
	}

	public void push() {
		relations.forEach((s, relation) -> relation.push());
		++stackDepth;
	}

	public void pop() {
		checkState(stackDepth > 0, "Cannot pop() if no push() was called!");
		relations.forEach((s, relation) -> relation.pop());
		--stackDepth;
	}

	/*
	 * Datalog program (facts, deduction rules and queries) in a basic String representation.
	 * Only supports queries of entire relations right now.
	 */
	public static String runProgram(String relations) {
		int counter = 0;
		Datalog datalog = new Datalog();
		StringBuilder ret = new StringBuilder();
		Map<String, Relation> relationMap = new LinkedHashMap<>();
		for (String expression : relations.split("\\.")) {
			String nospace = expression.replaceAll("[ \t\n]", "");
			if (nospace.matches("([a-z_][a-zA-Z0-9_]*)\\(([a-z_0-9][a-zA-Z0-9_]*)(,[a-z_0-9][a-zA-Z_0-9]*)*\\)")) { //fact assertion
				String[] splitString = nospace.split("\\(");
				String[] arguments = splitString[1].replaceAll("\\)", "").split(",");
				relationMap.putIfAbsent(splitString[0], datalog.createRelation("rel" + counter++, arguments.length));
				TupleN<DatalogArgument> argumentTuple = TupleN.of(Arrays.stream(arguments).map(StringDatalogArgument::new).collect(Collectors.toList()));
				relationMap.get(splitString[0]).addFact(argumentTuple);
			} else if (nospace.matches("([a-z_][a-zA-Z_0-9]*)\\(([a-zA-Z_][a-zA-Z0-9_]*)(,[a-zA-Z_][a-zA-Z0-9_]*)*\\):-([a-z_][a-zA-Z_]*)\\(([a-zA-Z_][a-zA-Z0-9_]*)(,[a-zA-Z_][a-zA-Z0-9_]*)*\\)(,([a-z_][a-zA-Z_]*)\\(([a-zA-Z_][a-zA-Z0-9_]*)(,[a-zA-Z_][a-zA-Z0-9_]*)*\\))*")) { //deduction rule
				String[] splitExpression = nospace.split(":-");

				Map<String, Variable> variableMap = new LinkedHashMap<>();
				String[] splitString = splitExpression[0].split("\\(");
				String[] arguments = splitString[1].replaceAll("\\)", "").split(",");
				relationMap.putIfAbsent(splitString[0], datalog.createRelation("rel" + counter++, arguments.length));
				TupleN<Variable> argumentTuple = TupleN.of(Arrays.stream(arguments).map(s -> {
					variableMap.putIfAbsent(s, datalog.getVariable());
					return variableMap.get(s);
				}).collect(Collectors.toList()));

				Set<Tuple2<Relation, TupleN<Variable>>> dependencies = new LinkedHashSet<>();
				for (String dependency : splitExpression[1].split("\\),")) {
					String[] dsplitString = dependency.split("\\(");
					String[] darguments = dsplitString[1].replaceAll("\\)", "").split(",");
					relationMap.putIfAbsent(dsplitString[0], datalog.createRelation("rel" + counter++, darguments.length));
					TupleN<Variable> dargumentTuple = TupleN.of(Arrays.stream(darguments).map(s -> {
						variableMap.putIfAbsent(s, datalog.getVariable());
						return variableMap.get(s);
					}).collect(Collectors.toList()));
					dependencies.add(Tuple2.of(relationMap.get(dsplitString[0]), dargumentTuple));
				}
				relationMap.get(splitString[0]).addRule(argumentTuple, dependencies);

			} else if (nospace.matches("([a-z_][a-zA-Z_]*)\\?")) { //query
				String noquestion = nospace.replaceAll("\\?", "");
				if (!relationMap.containsKey(noquestion))
					throw new RuntimeException("Query " + nospace + " does not query an existing relation!");
				for (TupleN<DatalogArgument> element : relationMap.get(noquestion).getElements()) {
					StringBuilder stringBuilder = new StringBuilder(noquestion + "(");
					for (Object o : element) {
						stringBuilder.append(o.toString()).append(",");
					}
					ret.append(stringBuilder.substring(0, stringBuilder.length() - 1)).append(").").append("\r\n");
				}
			} else {
				throw new RuntimeException("Input " + nospace + " does not match any type of expression!");
			}
		}
		return ret.toString();
	}

	private void refresh() {
		int cnt;
		do {
			cnt = 0;
			for (Relation relation : relations.values()) {
				int i = relation.calc();
				if (debug)
					System.out.println(i + " new facts");
				cnt += i;
			}
			if (debug)
				System.out.println("====");
		} while (cnt > 0);
		for (Relation relation : relations.values()) {
			relation.flush();
		}
	}

	public Relation createRelation(String name, int n) {
		checkState(stackDepth == 0, "Cannot create a relation when the program is in temporary (pushed) state");
		checkState(n > 0, "Relation must have positive arity");
		Relation ret = new Relation(n);
		relations.put(name, ret);
		return ret;
	}

	public Relation createTransitive(String name, Relation simple) {
		checkState(simple.arity == 2, "Only binary relations should have transitive closures!");
		Relation path = createRelation(name, 2);
		Datalog.Variable var1, var2, var3;
		path.addRule(
				TupleN.of(
						var1 = getVariable(),
						var2 = getVariable()
				),
				Set.of(
						Tuple2.of(
								simple,
								TupleN.of(var1, var2)
						)
				)
		);
		path.addRule(
				TupleN.of(
						var1 = getVariable(),
						var2 = getVariable()
				),
				Set.of(
						Tuple2.of(
								path,
								TupleN.of(
										var1,
										var3 = getVariable()
								)
						),
						Tuple2.of(
								path,
								TupleN.of(
										var3,
										var2
								)
						)
				)
		);
		return path;
	}

	public Relation createDisjunction(String name, Iterable<Relation> relations) {
		Integer arity = null;
		for (Relation relation : relations) {
			if(arity == null) arity = relation.getArity();
			else checkState(relation.getArity() == arity, "Only same arity relations are supported!");
		}
		checkState(arity != null, "At least one relation is necessary!");
		Relation disjunction = createRelation(name, arity);
		List<Variable> vars = new ArrayList<>();
		for (int i = 0; i < arity; i++) {
			vars.add(getVariable());
		}
		TupleN<Variable> varTuple = TupleN.of(vars);
		for (Relation relation : relations) {
			disjunction.addRule(
					varTuple,
					Set.of(
							Tuple2.of(
									relation,
									varTuple
							)
					)
			);
		}
		return disjunction;
	}
	public Relation createConjuction(String name, Iterable<Relation> relations) {
		Integer arity = null;
		TupleN<Variable> varTuple = null;
		Set<Tuple2<Relation, TupleN<Variable>>> deps = new LinkedHashSet<>();
		for (Relation relation : relations) {
			if(arity == null){
				arity = relation.getArity();
				List<Variable> vars = new ArrayList<>();
				for (int i = 0; i < arity; i++) {
					vars.add(getVariable());
				}
				varTuple = TupleN.of(vars);
			}
			else checkState(relation.getArity() == arity, "Only same arity relations are supported!");

			deps.add(Tuple2.of(relation, varTuple));
		}
		checkState(arity != null, "At least one relation is necessary!");
		Relation conjuction = createRelation(name, arity);
		conjuction.addRule(
				varTuple,
				deps
		);
		return conjuction;
	}

	public boolean isDebug() {
		return debug;
	}

	public void setDebug(boolean debug) {
		this.debug = debug;
	}

	public Variable getVariable() {
		return new Variable();
	}

	public static class Variable {
	}

	public class Relation {
		private String name;
		private final Set<TupleN<DatalogArgument>> elements;
		private final Set<TupleN<DatalogArgument>> newElements;
		private final Set<TupleN<DatalogArgument>> toAdd;
		private final Set<Tuple2<TupleN<Variable>, Set<Tuple2<Relation, TupleN<Variable>>>>> rules;
		private final int arity;
		private final Stack<Tuple3<Set<TupleN<DatalogArgument>>, Set<TupleN<DatalogArgument>>, Set<TupleN<DatalogArgument>>>> stack;

		private Relation(int n) {
			this("", n);
		}

		public void setName(String name) {
			this.name = name;
		}

		private Relation(String name, int n) {
			this.name = name;
			this.arity = n;
			elements = new LinkedHashSet<>();
			newElements = new LinkedHashSet<>();
			rules = new LinkedHashSet<>();
			toAdd = new LinkedHashSet<>();
			stack = new Stack<>();
		}

		public void addFact(TupleN<DatalogArgument> fact) {
			checkState(fact.arity() == arity);
			newElements.add(fact);
			if (debug) {
				System.out.println();
				System.out.println("New fact (" + name + "): " + fact);
			}
			refresh();
		}

		public void addRule(TupleN<Variable> args, Set<Tuple2<Relation, TupleN<Variable>>> dependencies) {
			checkState(stackDepth == 0, "Cannot create new rule when the program is in temporary (pushed) state");
			checkState(args.arity() == arity);
			for (Tuple2<Relation, TupleN<Variable>> dependency : dependencies) {
				checkState(dependency.get1().arity == dependency.get2().arity());
			}
			rules.add(Tuple2.of(args, new LinkedHashSet<>(dependencies)));
			refresh();
		}

		public Collection<TupleN<DatalogArgument>> getElements() {
			ArrayList<TupleN<DatalogArgument>> ret = new ArrayList<>(elements);
			ret.addAll(newElements);
			return ImmutableList.copyOf(ret);
		}

		public int getArity() {
			return arity;
		}

		private boolean validate(List<Tuple2<Relation, TupleN<Variable>>> oldClauses, Map<Variable, DatalogArgument> currentAssignments, List<Map<Variable, DatalogArgument>> assignments) {
			List<Tuple2<Relation, TupleN<Variable>>> clauses = new ArrayList<>(oldClauses);
			if (clauses.size() > 0) {
				Tuple2<Relation, TupleN<Variable>> clause = clauses.get(0);
				clauses.remove(0);
				for (TupleN<DatalogArgument> element : clause.get1().elements) {
					Map<Variable, DatalogArgument> nextAssignments = new LinkedHashMap<>(currentAssignments);
					if (!putAssignments(nextAssignments, clause, element)) {
						validate(clauses, nextAssignments, assignments);
					}
				}
				for (TupleN<DatalogArgument> element : clause.get1().newElements) {
					Map<Variable, DatalogArgument> nextAssignments = new LinkedHashMap<>(currentAssignments);
					if (!putAssignments(nextAssignments, clause, element)) {
						validate(clauses, nextAssignments, assignments);
					}
				}
				return assignments.size() > 0;
			} else {
				assignments.add(currentAssignments);
				return true;
			}
		}

		private int calc() {
			int cnt = 0;
			for (Tuple2<TupleN<Variable>, Set<Tuple2<Relation, TupleN<Variable>>>> rule : rules) {
				for (Tuple2<Relation, TupleN<Variable>> clause : rule.get2()) {
					Set<TupleN<DatalogArgument>> alreadyAdded = new LinkedHashSet<>();
					boolean atLeastOne = true;
					while(atLeastOne) {
						atLeastOne = false;
						for (TupleN<DatalogArgument> newElement : clause.get1().newElements.stream().filter(objects -> !alreadyAdded.contains(objects)).collect(Collectors.toCollection( LinkedHashSet::new ))) {
							cnt = addElements(cnt, rule, clause, newElement);
							alreadyAdded.add(newElement);
							atLeastOne = true;
						}
					}
					alreadyAdded.clear();
					atLeastOne = true;
					while(atLeastOne) {
						atLeastOne = false;
						for (TupleN<DatalogArgument> newElement : clause.get1().toAdd.stream().filter(objects -> !alreadyAdded.contains(objects)).collect(Collectors.toCollection( LinkedHashSet::new ))) {
							cnt = addElements(cnt, rule, clause, newElement);
							alreadyAdded.add(newElement);
							atLeastOne = true;
						}
					}
				}
			}
			return cnt;
		}

		private int addElements(int cnt, Tuple2<TupleN<Variable>, Set<Tuple2<Relation, TupleN<Variable>>>> rule, Tuple2<Relation, TupleN<Variable>> clause, TupleN<DatalogArgument> newElement) {
			Map<Variable, DatalogArgument> assignments = new LinkedHashMap<>();
			if (putAssignments(assignments, clause, newElement))
				return cnt;
			if (debug) {
				 System.out.println("\t(" + name + ")Checking " + newElement);
			}
			ArrayList<Tuple2<Relation, TupleN<Variable>>> validators = new ArrayList<>(rule.get2());
			validators.remove(clause);
			List<Map<Variable, DatalogArgument>> satisfyingAssignments = new ArrayList<>();
			if (validate(validators, assignments, satisfyingAssignments)) {
				for (Map<Variable, DatalogArgument> satisfyingAssignment : satisfyingAssignments) {
					List<DatalogArgument> arguments = new ArrayList<>();
					for (Object o : rule.get1()) {
						Variable v = (Variable) o;
						checkState(satisfyingAssignment.containsKey(v), "Not all variables are bound!");
						arguments.add(satisfyingAssignment.get(v));
					}
					TupleN<DatalogArgument> item = TupleN.of(arguments);
					if (!elements.contains(item) && !newElements.contains(item) && !toAdd.contains(item)) {
						toAdd.add(item);
						if (debug) {
							 System.out.println("(" + name + ")Adding " + item);
						}
						++cnt;
					}
				}

			}
			return cnt;
		}

		private boolean putAssignments(Map<Variable, DatalogArgument> assignments, Tuple2<Relation, TupleN<Variable>> validatorClause, TupleN<DatalogArgument> element) {
			for (int i = 0; i < element.arity(); i++) {
				if (assignments.containsKey(validatorClause.get2().get(i))) {
					if (!assignments.get(validatorClause.get2().get(i)).equals(element.get(i))) return true;
				} else {
					assignments.put(validatorClause.get2().get(i), element.get(i));
				}
			}
			return false;
		}

		private void flush() {
			if (debug) {
				StringBuilder stringBuilder = new StringBuilder("[");
				newElements.forEach(objects -> stringBuilder.append(objects.toString()).append(", "));
				
					System.out.println("(" + name + ") Promoting newElements to elements: " + stringBuilder.append("]").toString());
			}
			elements.addAll(newElements);
			newElements.clear();

			if (debug) {
				StringBuilder stringBuilder1 = new StringBuilder("[");
				toAdd.forEach(objects -> stringBuilder1.append(objects.toString()).append(", "));
				
					System.out.println("(" + name + ") Promoting toAdd to newElements: " + stringBuilder1.append("]").toString());
			}
			newElements.addAll(toAdd);
			toAdd.clear();
		}


		public void push() {
			stack.push(Tuple3.of(elements, newElements, toAdd));
		}

		public void pop() {
			final Tuple3<Set<TupleN<DatalogArgument>>, Set<TupleN<DatalogArgument>>, Set<TupleN<DatalogArgument>>> popped = stack.pop();
			elements.clear();
			elements.addAll(popped.get1());
			newElements.clear();
			newElements.addAll(popped.get2());
			toAdd.clear();
			toAdd.addAll(popped.get3());

		}
	}
}
