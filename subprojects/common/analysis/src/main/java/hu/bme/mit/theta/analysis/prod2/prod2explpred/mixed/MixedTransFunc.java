package hu.bme.mit.theta.analysis.prod2.prod2explpred.mixed;

import com.google.common.base.Preconditions;
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
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static java.util.Collections.singleton;

public class MixedTransFunc<A extends StmtAction> implements TransFunc<Prod2State<ExplState, PredState>, A, Prod2Prec<ExplPrec, PredPrec>> {

    private final Solver solver;

    private MixedTransFunc(final Solver solver) {
        this.solver = solver;
    }

    public static <A extends StmtAction> MixedTransFunc<A> create(final Solver solver) {
        return new MixedTransFunc<A>(solver);
    }

    @Override
    public Collection<? extends Prod2State<ExplState, PredState>> getSuccStates(Prod2State<ExplState, PredState> state,
                                                                                A action, Prod2Prec<ExplPrec, PredPrec> prec) {
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
            // TODO make more efficient
            final Map<VarDecl<?>, Integer> predCounts = Containers.createMap();
            prec.getPrec2().getPreds().forEach(
                    pred -> ExprUtils.getVars(pred).forEach(
                            decl -> predCounts.put(decl, predCounts.getOrDefault(decl, 0) + 1)
                    )
            );

            final List<VarDecl<?>> remainingVarsOrdered = prec.getPrec1().getVars().stream()
                    .filter(Predicate.not(val.getDecls()::contains))
                    .sorted(Comparator.comparingInt(decl -> predCounts.getOrDefault(decl, 0)))
                    .collect(Collectors.toList());

            if (remainingVarsOrdered.isEmpty()) {
                return singleton(Prod2State.of(ExplState.of(val), PredState.of()));
            }

            // Build assignment graph for remaining vars
            final VariableAssignmentNode root = VariableAssignmentNode.of(val, remainingVarsOrdered, Containers.createSet());
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

                final Expr<BoolType> expr = And(ExprUtils.applyPrimes(node.getValuation().toExpr(), action.nextIndexing()), action.toExpr(), state.toExpr());

                final var temporaryPrec = ExplPrec.of(ImmutableList.of(decl));
                final var maxSuccToEnumerate = (1 << predCounts.getOrDefault(decl, 0));
                final Collection<ExplState> succStates = ExprStates.createStatesForExpr(solver, expr, 0,
                        temporaryPrec::createState, action.nextIndexing(), maxSuccToEnumerate + 1);

                if (succStates.isEmpty()) {
                    return singleton(Prod2State.of(ExplState.bottom(), PredState.bottom()));
                } else if (succStates.size() <= maxSuccToEnumerate) {
                    final Set<VariableAssignmentNode> children = Containers.createSet();
                    for (var assignment : succStates) {
                        final var valueOpt = assignment.eval(decl);
                        final var valuation = MutableValuation.copyOf(node.getValuation());
                        Preconditions.checkArgument(valueOpt.isPresent(), "No value assigned to variable!");
                        valuation.put(decl, valueOpt.get());
                        children.add(VariableAssignmentNode.of(valuation, remaining, node.getPredicateTracked()));
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
                if(tuple.get2().isEmpty()){
                    mixedStates.add(Prod2State.of(ExplState.of(tuple.get1()), PredState.of(True())));
                } else {
                    final Set<Expr<BoolType>> remainingPredicates = prec.getPrec2().getPreds().stream()
                            .filter(pred -> !Collections.disjoint(ExprUtils.getVars(pred), tuple.get2()))
                            .collect(Collectors.toSet());

                    final Expr<BoolType> expr = And(ExprUtils.applyPrimes(tuple.get1().toExpr(), action.nextIndexing()), action.toExpr(), state.toExpr());
                    final PredPrec temporaryPrec = PredPrec.of(remainingPredicates);
                    final var abstractor = PredAbstractors.cartesianAbstractor(solver);
                    final var succStates = abstractor.createStatesForExpr(
                            expr, VarIndexing.all(0), temporaryPrec, action.nextIndexing());
                    succStates.forEach(predState -> mixedStates.add(Prod2State.of(ExplState.of(tuple.get1()),predState)));
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

}
