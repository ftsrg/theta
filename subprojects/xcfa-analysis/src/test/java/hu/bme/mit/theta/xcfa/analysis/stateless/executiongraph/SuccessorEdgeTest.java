package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.mcm.EmptyConstraint;
import hu.bme.mit.theta.mcm.graphfilter.*;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Fence;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Read;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Write;

import java.util.Set;

public class SuccessorEdgeTest {

    public static void main(String[] args) {
        EmptyConstraint emptyConstraint;
        while(true) {
            ForEachNode forEachNode = new ForEachNode(new NamedNode(Fence.class));
            SuccessorEdge successorEdge = new SuccessorEdge(
                    new Source(new SuccessorEdge(new NamedNode(Read.class), new NodeTag(forEachNode), Set.of("po"))),
                    new Target(new SuccessorEdge(new NodeTag(forEachNode), new NamedNode(Read.class), Set.of("po"))),
                    Set.of("po"));
            forEachNode.setOp(successorEdge);

            emptyConstraint = new EmptyConstraint(forEachNode, false, "fence");

            Write initWrite1 = new MockWrite();
            Write initWrite2 = new MockWrite();
            Write write1 = new MockWrite();
            Write write2 = new MockWrite();
            Read read1 = new MockRead();
            Read read2 = new MockRead();
            Fence fence1 = new MockFence();
            Fence fence2 = new MockFence();
            emptyConstraint.checkMk(initWrite1, write1, "po", true);
            emptyConstraint.checkMk(initWrite1, read1, "po", true);
            emptyConstraint.checkMk(initWrite2, read1, "po", true);
            emptyConstraint.checkMk(initWrite2, write1, "po", true);
            emptyConstraint.checkMk(read1, fence1, "po", true);
            emptyConstraint.checkMk(fence1, read2, "po", true);
            emptyConstraint.checkMk(write1, fence2, "po", true);
            emptyConstraint.checkMk(fence2, write2, "po", true);
        }
    }
}
