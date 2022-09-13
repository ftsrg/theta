package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.DdLevel;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.java.mdd.impl.MddVariableImpl;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.IncompleteMddSymbolicNodeInterpretation;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeImpl;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.TraversalConstraint;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * This class will be a descendant of the {@link MddVariable} class once the 'final' keyword is removed.
 */
public class ExprVariable implements MddVariable {
    private final MddVariableOrder variableOrder;
    private final DdLevel<MddNode> level;
    private final DdLevel<MddNode>        primedLevel;
    private final MddCanonizationStrategy canonizationStrategy;
    private final Object                  traceInfo;

    private      MddVariable             lower;
    private                int                     domainSize;
    private final          boolean                 fixedDomain;

    private final Supplier<Solver> solverSupplier;

    ExprVariable(
            @Nonnull MddVariableOrder variableOrder,
            @Nonnull hu.bme.mit.delta.mdd.MddVariableDescriptor variableDescription,
            @Nonnull DdLevel<MddNode> level,
            @Nonnull DdLevel<MddNode> primedLevel,
            @Nonnull Supplier<Solver> solverSupplier
    ) {
        Preconditions.checkNotNull(variableOrder, "variableOrder");
        Preconditions.checkNotNull(variableDescription, "variableDescription");
        Preconditions.checkNotNull(level, "level");
        this.traceInfo = variableDescription.getTraceInfo();
        this.domainSize = variableDescription.getDomainSize();
        this.fixedDomain = variableDescription.isBounded();
        this.variableOrder = variableOrder;
        this.level = level;
        this.primedLevel = primedLevel;
        if (variableDescription instanceof MddVariableDescriptor) {
            this.canonizationStrategy = ((MddVariableDescriptor) variableDescription).getCanonizationStrategy();
        } else {
            this.canonizationStrategy = MddCanonizationStrategy.defaultStrategy();
        }
        this.solverSupplier = solverSupplier;
    }

    @Override
    public MddNode checkInNode(IntObjMapView<? extends MddNode> intObjMapView) {
        return null;
    }

    @Override
    public IntObjMapView<MddNode> getNodeInterpreter(MddNode node) {
        if(node instanceof MddSymbolicNodeImpl){
            MddSymbolicNodeImpl symbolicNode = (MddSymbolicNodeImpl) node;
            if (!symbolicNode.isOn(this)) {
                if (!symbolicNode.isBelow(this)) {
                    throw new AssertionError();
                }

                IntObjMapView<MddNode> nodeInterpreter = IntObjMapView.empty(symbolicNode);
                if (this.isBounded()) {
                    nodeInterpreter = ((IntObjMapView)nodeInterpreter).trim(IntSetView.range(0, this.getDomainSize()));
                }
                return nodeInterpreter;
            }

            if(symbolicNode.isComplete()){
                return symbolicNode.getCacheView();
            } else {
                final Expr<?> expr = symbolicNode.getSymbolicRepresentation(Expr.class).first;
                // TODO this check should only be done once per node
                // TODO this is not the right place for this check
                if(!ExprUtils.getConstants(expr).contains(symbolicNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class))){
                    final MddSymbolicNodeImpl childNode = ExprNodeUtils.uniqueTable.checkIn(new MddSymbolicNodeImpl(new Pair<>(expr,symbolicNode.getSymbolicRepresentation().second.getLower().orElse(null))));
                    if(symbolicNode.getCacheView().defaultValue() != null) Preconditions.checkState(symbolicNode.getCacheView().defaultValue().equals(childNode));
                    else {
                        symbolicNode.getExplicitRepresentation().cacheDefault(childNode);
                        symbolicNode.getExplicitRepresentation().setComplete();
                    }
                    return symbolicNode.getCacheView();
                }
                return new IncompleteMddSymbolicNodeInterpretation(symbolicNode, getNodeTraverser(symbolicNode));
            }
        }

        throw new UnsupportedOperationException("Not yet implemented!");
    }

    public MddNode checkInNode(MddSymbolicNodeImpl.SymbolicRepresentation template) {
        return level.checkIn(template, sr -> new MddSymbolicNodeImpl((MddSymbolicNodeImpl.SymbolicRepresentation) sr));
    }

    public MddSymbolicNodeTraverser getNodeTraverser(MddSymbolicNodeImpl node){
        return new ExprNodeTraverser(node, solverSupplier);
    }

    public MddSymbolicNodeTraverser getConstrainedNodeTraverser(MddSymbolicNodeImpl node, TraversalConstraint constraint){
        return new ConstrainedExprNodeTraverser(node, solverSupplier, constraint);
    }

    //Innentől MddVariableImplből lopva
    @Override
    public DdLevel<MddNode> getLevel() {
        return level;
    }

    @Override
    public DdLevel<MddNode> getPrimedLevel() {
        return primedLevel;
    }

    @Override
    public MddVariableOrder getMddVariableOrder() {
        return variableOrder;
    }

    @Nonnull
    @Override
    public Optional<? extends MddVariable> getLower() {
        return Optional.ofNullable(lower);
    }

    @Override
    public void setLower(@Nonnull final MddVariable lower) {
        Preconditions.checkNotNull(lower, "lower");
        if (this.lower != null) {
            Preconditions.checkArgument(
                    this.lower.isBelow(lower),
                    "The new lower neighbor must already be above the current lower neighbor. Make sure that you insert" +
                            " new elements by first setting their lower neighbor and then modifying the lower neighbor of this element."
            );
        }
        this.lower = lower;
    }

    @Override
    public Object getTraceInfo() {
        return traceInfo;
    }

    @Override
    public int getDomainSize() {
        return domainSize;
    }

    @Override
    public boolean isBounded() {
        return fixedDomain;
    }

    @Override
    public int hashCode() {
        return traceInfo.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ExprVariable) {
            return this.traceInfo.equals(((ExprVariable) obj).getTraceInfo());
        }
        return false;
    }

}
