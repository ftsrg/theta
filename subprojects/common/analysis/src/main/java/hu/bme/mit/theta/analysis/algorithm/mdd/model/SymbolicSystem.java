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
package hu.bme.mit.theta.analysis.algorithm.mdd.model;

import java.util.ArrayList;
import java.util.List;

public interface SymbolicSystem {
    public static SymbolicSystem simpleSystemOf(final List<Component> componentOrder,
                                                final AbstractNextStateDescriptor nextStateDescriptorRoot,
                                                final AbstractNextStateDescriptor initializerDescriptorRoot) {
        return new SymbolicSystem() {
            final List<Component> compOrder = new ArrayList<Component>(componentOrder);

            @Override
            public AbstractNextStateDescriptor getNextStateDescriptorRoot() {
                return nextStateDescriptorRoot;
            }

            @Override
            public AbstractNextStateDescriptor getInitializerDescriptorRoot() {
                return initializerDescriptorRoot;
            }

            @Override
            public List<Component> getComponentOrder() {
                return compOrder;
            }
        };
    }

    public List<Component> getComponentOrder();

    public AbstractNextStateDescriptor getNextStateDescriptorRoot();

    public AbstractNextStateDescriptor getInitializerDescriptorRoot();
}
