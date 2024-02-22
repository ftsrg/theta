/*
 *  Copyright 2024 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
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
