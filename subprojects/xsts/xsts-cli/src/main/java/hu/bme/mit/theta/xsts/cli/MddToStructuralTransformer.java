package hu.bme.mit.theta.xsts.cli;

import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate;

public class MddToStructuralTransformer {

    public static MddHandle transform(MddHandle mddHandle, MddVariableHandle variableHandle) {
        return transform(mddHandle, variableHandle, mddHandle.cursor());
    }

    public static MddHandle transform(MddHandle node, MddVariableHandle variable, RecursiveIntObjCursor<? extends MddHandle> cursor) {

        if (node.isTerminal()) {
            if (node.isTerminalZero()) {
                return variable.getMddGraph().getTerminalZeroHandle();
            } else {
                MddGraph<Object> mddGraph = (MddGraph<Object>) variable.getMddGraph();
                return mddGraph.getTerminalVariableHandle().getHandleFor(mddGraph.getNodeFor(node.getData()));
            }
        }

        MddUnsafeTemplateBuilder templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder();

        while (cursor.moveNext()) {

            try (var valueCursor = cursor.valueCursor()) {

                MddHandle s = transform(cursor.value(),
                        variable.getLower().orElse(null), valueCursor
                );

                templateBuilder.set(cursor.key(), s.getNode());
            }
        }

        return variable.checkInNode(MddStructuralTemplate.of(templateBuilder.buildAndReset()));

    }

}
