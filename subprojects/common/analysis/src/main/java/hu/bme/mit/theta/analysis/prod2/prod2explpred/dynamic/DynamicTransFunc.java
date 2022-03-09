package hu.bme.mit.theta.analysis.prod2.prod2explpred.dynamic;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.StmtApplier;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.pred.PredAbstractors;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static java.util.Collections.singleton;

public class DynamicTransFunc<A extends StmtAction> implements TransFunc<Prod2State<ExplState, PredState>, A, DynamicPrec> {

    private final Solver solver;

    private DynamicTransFunc(final Solver solver) {
        this.solver = solver;
    }

    public static <A extends StmtAction> DynamicTransFunc<A> create(final Solver solver) {
        return new DynamicTransFunc<A>(solver);
    }

    @Override
    public Collection<? extends Prod2State<ExplState, PredState>> getSuccStates(Prod2State<ExplState, PredState> state,
                                                                                A action, DynamicPrec prec) {
        checkNotNull(state);
        checkNotNull(action);
        checkNotNull(prec);

        checkArgument(action.getStmts().size() == 1, "Only implemented for a single stmt per action");
        final Stmt stmt = action.getStmts().get(0);

        // 1.: Best-effort statement applying
        final MutableValuation val = MutableValuation.copyOf(state.getState1());
        final StmtApplier.ApplyResult applyResult = StmtApplier.apply(stmt, val, true);

        if (applyResult == StmtApplier.ApplyResult.BOTTOM) {
            return singleton(Prod2State.of(ExplState.bottom(), PredState.bottom()));
        } else {
            final List<VarDecl<?>> remainingVarsOrdered = prec.getPrec1().getVars().stream()
                    .filter(Predicate.not(val.getDecls()::contains))
                    .sorted(Comparator.comparingInt(prec::getPredCount))
                    .collect(Collectors.toList());

            if (remainingVarsOrdered.isEmpty()) {
                return singleton(Prod2State.of(ExplState.of(projectValuation(val, prec.getPrec1())), PredState.of(True())));
            }

            // Build assignment graph for remaining vars
            final VariableAssignmentNode root = VariableAssignmentNode.of(projectValuation(val, prec.getPrec1()), remainingVarsOrdered, Containers.createSet()); // TODO decide if projection needed
            final Waitlist<VariableAssignmentNode> waitlist = FifoWaitlist.create(ImmutableList.of(root));
            final Set<Tuple2<Valuation, Set<VarDecl<?>>>> branches = Containers.createSet();

            while (!waitlist.isEmpty()) {
                final var node = waitlist.remove();
                final var remaining = new LinkedList<>(node.getRemainingVarsOrdered());
                if (remaining.isEmpty()) {
                    branches.add(Tuple2.of(node.getValuation(), node.getPredicateTracked()));
                    continue;
                }
                var decl = remaining.removeFirst();

                // TODO write expr simplifier function that can replace primed refexprs
                final Expr<BoolType> expr = And(ExprUtils.applyPrimes(node.getValuation().toExpr(), action.nextIndexing()), action.toExpr(), state.toExpr());

                final var temporaryPrec = ExplPrec.of(ImmutableList.of(decl));
                int maxSuccToEnumerate = (1 << prec.getPredCount(decl));
                if(maxSuccToEnumerate < 0) maxSuccToEnumerate = 0;
                final Collection<ExplState> succStates = ExprStates.createStatesForExpr(solver, expr, 0,
                        temporaryPrec::createState, action.nextIndexing(), maxSuccToEnumerate + 1);

                if (succStates.isEmpty()) {
                    // Drop this branch of the tree
                    continue;
                } else if (succStates.size() <= maxSuccToEnumerate) {
                    final Set<VariableAssignmentNode> children = Containers.createSet();
                    for (var assignment : succStates) {
                        final var valueOpt = assignment.eval(decl);
                        if (valueOpt.isPresent()) {
                            final var valuation = MutableValuation.copyOf(node.getValuation());
                            valuation.put(decl, valueOpt.get());
                            children.add(VariableAssignmentNode.of(valuation, remaining, node.getPredicateTracked()));
                        } else {
//                            var predicateTracked = Containers.createSet(node.getPredicateTracked());
//                            predicateTracked.add(decl);
                            var newNode = VariableAssignmentNode.of(node.getValuation(), remaining, node.getPredicateTracked());
                            waitlist.add(newNode);
                            node.expand(singleton(newNode));
                        }
                    }
                    waitlist.addAll(children);
                    node.expand(children);
                } else {
                    var predicateTracked = Containers.createSet(node.getPredicateTracked());
                    predicateTracked.add(decl);
                    var newNode = VariableAssignmentNode.of(node.getValuation(), remaining, predicateTracked);
                    waitlist.add(newNode);
                    node.expand(singleton(newNode));
                }
            }

            final Set<Prod2State<ExplState, PredState>> mixedStates = Containers.createSet();

            for (var tuple : branches) {
                if (tuple.get2().isEmpty()) {
                    mixedStates.add(Prod2State.of(ExplState.of(projectValuation(tuple.get1(), prec.getPrec1())), PredState.of(True())));
                } else {
                    final Set<Expr<BoolType>> remainingPredicates = prec.getPrec2().getPreds().stream()
                            .filter(pred -> !Collections.disjoint(ExprUtils.getVars(pred), tuple.get2()))
                            .collect(Collectors.toSet());

                    final Expr<BoolType> expr = And(ExprUtils.applyPrimes(tuple.get1().toExpr(), action.nextIndexing()), action.toExpr(), state.toExpr());

                    final PredPrec temporaryPrec = PredPrec.of(remainingPredicates);
                    final var abstractor = PredAbstractors.cartesianAbstractor(solver);
                    final var succStates = abstractor.createStatesForExpr(
                            expr, VarIndexing.all(0), temporaryPrec, action.nextIndexing());
                    final var succStatesSimplified = succStates.stream().map(
                            s -> PredState.of(ExprUtils.simplify(s.toExpr(), tuple.get1())) // TODO
                    ).collect(Collectors.toSet());
                    succStatesSimplified.forEach(predState -> mixedStates.add(Prod2State.of(ExplState.of(projectValuation(tuple.get1(), prec.getPrec1())), predState)));
                }
            }

            return mixedStates;
        }
    }

    private static class VariableAssignmentNode {

        private final Valuation valuation;

        private final List<VarDecl<?>> remainingVarsOrdered;

        private final Set<VarDecl<?>> predicateTracked;

        private final Set<VariableAssignmentNode> children = Containers.createSet();

        private VariableAssignmentNode(final Valuation valuation,
                                       final List<VarDecl<?>> remainingVarsOrdered,
                                       final Set<VarDecl<?>> predicateTracked) {
            this.valuation = ImmutableValuation.copyOf(valuation);
            this.remainingVarsOrdered = remainingVarsOrdered;
            this.predicateTracked = predicateTracked;
        }

        public static VariableAssignmentNode of(final Valuation valuation,
                                                final List<VarDecl<?>> remainingVarsOrdered,
                                                final Set<VarDecl<?>> predicateTracked) {
            return new VariableAssignmentNode(valuation, remainingVarsOrdered, predicateTracked);
        }

        public Valuation getValuation() {
            return valuation;
        }

        public List<VarDecl<?>> getRemainingVarsOrdered() {
            return remainingVarsOrdered;
        }

        public void expand(final Set<VariableAssignmentNode> children) {
            this.children.addAll(children);
        }

        public Set<VarDecl<?>> getPredicateTracked() {
            return predicateTracked;
        }
    }

    private static Valuation projectValuation(Valuation val, ExplPrec prec) {
        final var valAsMap = val.toMap();
        final MutableValuation newVal = new MutableValuation();
        for (var decl : prec.getVars()) {
            if (valAsMap.containsKey(decl)) newVal.put(decl, valAsMap.get(decl));
        }
        return newVal;
    }

}
