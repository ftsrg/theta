package hu.bme.mit.theta.common;

/*
 * Datalog engine using naive (enumerative) evaluation.
 * Limitations:
 *  - Only relations are supported right now, simple atoms are not
 *  - There is a performance penalty for specific rulesets, see
 *    http://pages.cs.wisc.edu/~paris/cs838-s16/lecture-notes/lecture8.pdf
 */

import com.google.common.collect.ImmutableList;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class Datalog {
    private final List<Relation> relations;
    private boolean debug = false;
    public static Datalog createProgram() {
        return new Datalog();
    }

    private Datalog() {
        relations = new ArrayList<>();
    }

    private void refresh() {
        int cnt;
        do {
            cnt = 0;
            for (Relation relation : relations) {
                int i = relation.calc();
                if(debug)
                    System.out.println(i + " new facts");
                cnt+=i;
            }
            if(debug)
                System.out.println("====");
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

    public boolean isDebug() {
        return debug;
    }

    public void setDebug(boolean debug) {
        this.debug = debug;
    }

    public class Relation{
        private final Set<TupleN<DatalogArgument>> elements;
        private final Set<TupleN<DatalogArgument>> newElements;
        private final Set<TupleN<DatalogArgument>> toAdd;
        private final Set<Tuple2<TupleN<Variable>, Set<Tuple2<Relation,TupleN<Variable>>>>> rules;
        private final int arity;

        private Relation(int n) {
            this.arity = n;
            elements = new LinkedHashSet<>();
            newElements = new LinkedHashSet<>();
            rules = new LinkedHashSet<>();
            toAdd = new LinkedHashSet<>();
        }

        public void addFact(TupleN<DatalogArgument> fact){
            checkState(fact.arity() == arity);
            newElements.add(fact);
            if(debug){
                System.out.println();
                System.out.println("New fact: " + fact);
            }
            refresh();
        }

        public void addRule(TupleN<Variable> args, Set<Tuple2<Relation,TupleN<Variable>>> dependencies) {
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

        private boolean validate(List<Tuple2<Relation, TupleN<Variable>>> clauses, Map<Variable, DatalogArgument> currentAssignments, List<Map<Variable, DatalogArgument>> assignments) {
            if(clauses.size() > 0) {
                Tuple2<Relation, TupleN<Variable>> clause = clauses.get(0);
                clauses.remove(0);
                for (TupleN<DatalogArgument> element : clause.get1().elements) {
                    Map<Variable, DatalogArgument> nextAssignments = new HashMap<>(currentAssignments);
                    if (!putAssignments(nextAssignments, clause, element)) {
                        validate(clauses, nextAssignments, assignments);
                    }
                }
                for (TupleN<DatalogArgument> element : clause.get1().newElements) {
                    Map<Variable, DatalogArgument> nextAssignments = new HashMap<>(currentAssignments);
                    if (!putAssignments(nextAssignments, clause, element)) {
                        validate(clauses, nextAssignments, assignments);
                    }
                }
                return assignments.size() > 0;
            }
            else {
                assignments.add(currentAssignments);
                return true;
            }
        }

        private int calc() {
            int cnt = 0;
            for (Tuple2<TupleN<Variable>, Set<Tuple2<Relation, TupleN<Variable>>>> rule : rules) {
                for (Tuple2<Relation, TupleN<Variable>> clause : rule.get2()) {
                    for (TupleN<DatalogArgument> newElement : clause.get1().newElements) {
                        cnt = addElements(cnt, rule, clause, newElement);
                    }
                    for (TupleN<DatalogArgument> newElement : clause.get1().toAdd) {
                        cnt = addElements(cnt, rule, clause, newElement);
                    }
                }
            }
            return cnt;
        }

        private int addElements(int cnt, Tuple2<TupleN<Variable>, Set<Tuple2<Relation, TupleN<Variable>>>> rule, Tuple2<Relation, TupleN<Variable>> clause, TupleN<DatalogArgument> newElement) {
            Map<Variable, DatalogArgument> assignments = new HashMap<>();
            if (putAssignments(assignments, clause, newElement))
                return cnt;
            if(debug) {
                if (this == relations.get(1)) System.out.println("\tChecking " + newElement);
            }
            ArrayList<Tuple2<Relation, TupleN<Variable>>> validators = new ArrayList<>(rule.get2());
            validators.remove(clause);
            List<Map<Variable, DatalogArgument>> satisfyingAssignments = new ArrayList<>();
            if(validate(validators, assignments, satisfyingAssignments)) {
                for (Map<Variable, DatalogArgument> satisfyingAssignment : satisfyingAssignments) {
                    List<DatalogArgument> arguments = new ArrayList<>();
                    for (Object o : rule.get1()) {
                        Variable v = (Variable) o;
                        checkState(satisfyingAssignment.containsKey(v), "Not all variables are bound!");
                        arguments.add(satisfyingAssignment.get(v));
                    }
                    TupleN<DatalogArgument> item = TupleN.of(arguments);
                    if(!elements.contains(item) && !newElements.contains(item) && !toAdd.contains(item)) {
                        toAdd.add(item);
                        if(debug) {
                            if (this == relations.get(1)) System.out.println("Adding " + item);
                        }
                        ++cnt;
                    }
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
            if(debug) {
                StringBuilder stringBuilder = new StringBuilder("[");
                newElements.forEach(objects -> stringBuilder.append(objects.toString()).append(", "));
                if (this == relations.get(1))
                    System.out.println("Promoting newElements to elements: " + stringBuilder.append("]").toString());
            }
            elements.addAll(newElements);
            newElements.clear();

            if(debug) {
                StringBuilder stringBuilder1 = new StringBuilder("[");
                toAdd.forEach(objects -> stringBuilder1.append(objects.toString()).append(", "));
                if (this == relations.get(1))
                    System.out.println("Promoting toAdd to newElements: " + stringBuilder1.append("]").toString());
            }
            newElements.addAll(toAdd);
            toAdd.clear();
        }


    }

    public Variable getVariable(){return new Variable();}

    public static class Variable {}
}
