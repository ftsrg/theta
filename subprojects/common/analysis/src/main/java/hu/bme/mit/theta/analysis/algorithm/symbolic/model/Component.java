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
package hu.bme.mit.theta.analysis.algorithm.symbolic.model;

import hu.bme.mit.delta.collections.IntCursor;

/**
 * Represents the components of the system under analysis, that is, fragments of
 * the system that has their own (local) state (the product of which is the
 * global state of the full system). Implementors may add every necessary
 * attributes and operations to support {@link AbstractNextStateDescriptor}
 * implementations. Shall contain a {@link DomainRegistry} to keep track of
 * discovered states of the component.
 *
 * @author Vince
 * @see AbstractNextStateDescriptor
 * @see DomainRegistry
 */
public interface Component {
    public static Component heterogeneousFrom(final Component... components) {
        return new Component() {

            @Override
            public DomainRegistry getDomainRegistry() {
                return new DomainRegistry() {

                    @Override
                    public boolean contains(final int v) {
                        return components[0].getDomainRegistry().contains(v);
                    }

                    @Override
                    public IntCursor cursor() {
                        return components[0].getDomainRegistry().cursor();
                    }

                    @Override
                    public boolean isEmpty() {
                        return components[0].getDomainRegistry().isEmpty();
                    }

                    @Override
                    public boolean isProcedural() {
                        return false;
                    }

                    @Override
                    public int size() {
                        return components[0].getDomainRegistry().size();
                    }

                    @Override
                    public void confirm(int value) {
                        for (Component c : components) {
                            c.getDomainRegistry().confirm(value);
                        }
                    }

                    @Override
                    public void clear() {
                        for (Component c : components) {
                            c.getDomainRegistry().clear();
                        }
                    }
                };
            }

            // @Override
            // public boolean correspondsTo(Component subComponent) {
            // 	for (int i = 0; i < components.length; ++i) {
            // 		if (components[i].correspondsTo(subComponent)) {
            // 			return true;
            // 		}
            // 	}
            // 	return false;
            // }

            @Override
            public Object getTraceInfo() {
                return components[0].getTraceInfo();
            }
        };
    }

    // TODO: possible tweaking. Is the explicit domain registry better than the bounded?

    /**
     * Gets the {@link DomainRegistry} that is associated with this component,
     * keeping track of the local states discovered so far.
     *
     * @return The {@link DomainRegistry} associated with this component.
     */
    public DomainRegistry getDomainRegistry();

    // /**
    //  * Returns true if this component is the same as {@code subComponent} or this
    //  * component is a composite component and contains {@code subComponent} (to
    //  * support heterogeneous {@link AbstractNextStateDescriptor} implementations)
    //  * and false otherwise.
    //  *
    //  * @param subComponent
    //  *            The component to checks (usually coming from an
    //  *            {@link AbstractNextStateDescriptor}).
    //  * @return True if {@code subComponent} is equivalent to this component or this
    //  *         component somehow contains or corresponds to {@code subComponent}.
    //  *
    //  * @see DomainRegistry
    //  */
    // public boolean correspondsTo(Component subComponent);

    Object getTraceInfo();

    default <T> T getTraceInfo(Class<T> typeToken) {
        return typeToken.cast(getTraceInfo());
    }
}
