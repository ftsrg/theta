package hu.bme.mit.theta.solver.smtlib.mathsat;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class MathSATSmtLibItpPattern implements ItpPattern.Binary<MathSATSmtLibItpMarker>, ItpPattern.Sequence<MathSATSmtLibItpMarker>, ItpPattern.Tree<MathSATSmtLibItpMarker> {
    final ItpMarkerTree<MathSATSmtLibItpMarker> markerTree;

    MathSATSmtLibItpPattern(final ItpMarkerTree<MathSATSmtLibItpMarker> markerTree) {
        this.markerTree = markerTree;
    }

    @SuppressWarnings("unchecked")
    static MathSATSmtLibItpPattern of(final ItpMarkerTree<? extends ItpMarker> markerTree) {
        final var list = new ArrayList<ItpMarkerTree<? extends ItpMarker>>();
        list.add(markerTree);
        while(!list.isEmpty()) {
            final var node = list.get(0);
            list.remove(0);

            checkArgument(node.getMarker() instanceof MathSATSmtLibItpMarker);

            list.addAll(node.getChildren());
        }

        return new MathSATSmtLibItpPattern((ItpMarkerTree<MathSATSmtLibItpMarker>) markerTree);
    }

    @Override
    public MathSATSmtLibItpMarker getA() {
        checkState(isBinary());
        return markerTree.getChild(0).getMarker();
    }

    @Override
    public MathSATSmtLibItpMarker getB() {
        checkState(isBinary());
        return markerTree.getMarker();
    }

    @Override
    public List<MathSATSmtLibItpMarker> getSequence() {
        checkState(isSequence());
        final var markerList = new ArrayList<MathSATSmtLibItpMarker>();

        var current = markerTree;
        while(current.getChildrenNumber() > 0) {
            markerList.add(current.getMarker());
            current = current.getChild(0);
        }
        markerList.add(current.getMarker());

        return Lists.reverse(markerList);
    }

    @Override
    public ItpMarkerTree<MathSATSmtLibItpMarker> getRoot() {
        return markerTree;
    }

    @Override
    public <E> E visit(ItpPatternVisitor<E> visitor) {
        return visitor.visitTreePattern(this);
    }

    private boolean isBinary() {
        return
            markerTree != null &&
            markerTree.getChildrenNumber() == 1 &&
            markerTree.getChild(0) != null &&
            markerTree.getChild(0).getChildrenNumber() == 0;
    }

    private boolean isSequence() {
        var current = markerTree;
        while(current.getChildrenNumber() > 0) {
            if(current.getChildrenNumber() > 1) {
                return false;
            }
            else {
                current = current.getChild(0);
            }
        }
        return true;
    }
}
