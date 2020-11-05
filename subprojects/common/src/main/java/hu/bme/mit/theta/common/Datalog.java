package hu.bme.mit.theta.common;

/*
 * Datalog engine using naive (enumerative) evaluation.
 * Limitations:
 *  - Only relations are supported right now, simple atoms are not
 */

import com.google.common.collect.ImmutableList;

import java.util.*;

import static com.google.common.base.Preconditions.checkState;

public class Datalog {
    private final List<Relation> relations;

    public static Datalog createProgram() {
        return new Datalog();
    }

    private Datalog() {
        relations = new ArrayList<>();
    }

    public void refresh() {
        int cnt = 0;
        do {
            cnt = 0;
            for (Relation relation : relations) {
                cnt+=relation.calc();
            }
        } while(cnt > 0);
        for (Relation relation : relations) {
            relation.flush();
        }
    }

    public Relation createRelation(int n) {
        checkState(n > 0, "Relation must have positive arity");
        Relation ret = new Relation(n);
        relations.add(ret);
        return ret;
    }

    public static class Relation{
        private final Set<TupleN<DatalogArgument>> elements;
        private final Set<TupleN<DatalogArgument>> newElements;
        private final Set<Tuple2<TupleN<Variable>, Set<Tuple2<Relation,TupleN<Variable>>>>> rules;
        private final int arity;

        private Relation(int n) {
            this.arity = n;
            elements = new LinkedHashSet<>();
            newElements = new LinkedHashSet<>();
            rules = new LinkedHashSet<>();
        }

        public void addFact(TupleN<DatalogArgument> fact){
            checkState(fact.arity() == arity);
            newElements.add(fact);
        }

        public void addRule(TupleN<Variable> args, Set<Tuple2<Relation,TupleN<Variable>>> dependencies) {
            checkState(args.arity() == arity);
            for (Tuple2<Relation, TupleN<Variable>> dependency : dependencies) {
                checkState(dependency.get1().arity == dependency.get2().arity());
            }
            rules.add(Tuple2.of(args, new LinkedHashSet<>(dependencies)));
        }

        public Collection<TupleN<DatalogArgument>> getElements() {
            return ImmutableList.copyOf(elements);
        }

        public int getArity() {
            return arity;
        }

        private int calc() { //TODO: rewrite recursively to allow for backtracking
            int cnt = 0;
            for (Tuple2<TupleN<Variable>, Set<Tuple2<Relation, TupleN<Variable>>>> rule : rules) {
                for (Tuple2<Relation, TupleN<Variable>> clause : rule.get2()) {
                    Set<TupleN<DatalogArgument>> toAdd = new LinkedHashSet<>();
                    midLoop:
                        for (TupleN<DatalogArgument> newElement : clause.get1().newElements) {
                            Map<Variable, DatalogArgument> assignments = new HashMap<>();
                            if (putAssignments(assignments, clause, newElement))
                                continue;
                            for (Tuple2<Relation, TupleN<Variable>> validatorClause : rule.get2()) {
                                boolean exists = false;
                                Map<Variable, DatalogArgument> validatorAssignments = new HashMap<>(assignments);

                                for (TupleN<DatalogArgument> element : validatorClause.get1().elements) {
                                    if (!putAssignments(validatorAssignments, validatorClause, element)) {
                                        exists = true;
                                        break; //should try the next available!
                                    }
                                }
                                if(!exists) {
                                    for (TupleN<DatalogArgument> element : validatorClause.get1().newElements) {
                                        if (!putAssignments(validatorAssignments, validatorClause, element)) {
                                            exists = true;
                                            break; //should try the next available!
                                        }
                                    }
                                }
                                if(exists) {
                                    assignments.putAll(validatorAssignments);
                                }
                                else {
                                    continue midLoop;
                                }
                            }
                            List<DatalogArgument> arguments = new ArrayList<>();
                            for (Object o : rule.get1()) {
                                Variable v = (Variable) o;
                                checkState(assignments.containsKey(v));
                                arguments.add(assignments.get(v));
                            }
                            TupleN<DatalogArgument> item = TupleN.of(arguments);
                            if(!elements.contains(item) && !newElements.contains(item) && !toAdd.contains(item)) {
                                toAdd.add(item);
                                ++cnt;
                            }
                        }
                    newElements.addAll(toAdd);
                }
            }
            return cnt;
        }

        private boolean putAssignments(Map<Variable, DatalogArgument> assignments, Tuple2<Relation, TupleN<Variable>> validatorClause, TupleN<DatalogArgument> element) {
            for (int i = 0; i < element.arity(); i++) {
                if(assignments.containsKey(validatorClause.get2().get(i))) {
                    if(!assignments.get(validatorClause.get2().get(i)).equals(element.get(i))) return true;
                }
                else {
                    assignments.put(validatorClause.get2().get(i), element.get(i));
                }
            }
            return false;
        }

        private void flush() {
            elements.addAll(newElements);
            newElements.clear();
        }


    }

    public Variable getVariable(){return new Variable();}

    public static class Variable {}
}
