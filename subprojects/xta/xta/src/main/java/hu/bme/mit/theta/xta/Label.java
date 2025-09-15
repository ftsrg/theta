/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.core.type.Type;
import java.util.List;

public final class Label {

    private static final int HASH_SEED = 8527;
    private volatile int hashCode = 0;

    private final String name;
    private final List<Type> paramTypes;
    private final boolean broadcast;

    private Label(
            final String name, final List<? extends Type> paramTypes, final boolean broadcast) {
        this.name = checkNotNull(name);
        this.paramTypes = ImmutableList.copyOf(checkNotNull(paramTypes));
        this.broadcast = broadcast;
    }

    public static Label of(
            final String name, final List<? extends Type> paramTypes, final boolean broadcast) {
        return new Label(name, paramTypes, broadcast);
    }

    public String getName() {
        return name;
    }

    public List<Type> getParamTypes() {
        return paramTypes;
    }

    public boolean isBroadcast() {
        return broadcast;
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + name.hashCode();
            result = 31 * result + paramTypes.hashCode();
            result = 31 * result + (broadcast ? 1 : 0);
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        return super.equals(obj);
    }

    @Override
    public String toString() {
        return name;
    }
}
