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
package hu.bme.mit.theta.core.parser;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.container.Containers;
import java.util.Map;
import java.util.function.Function;

public final class Env {

    private Frame currentFrame;

    public Env() {
        this.currentFrame = new Frame(null);
    }

    public void push() {
        currentFrame = new Frame(currentFrame);
    }

    public void pop() {
        checkState(currentFrame.parent != null, "No parent.");
        currentFrame = currentFrame.parent;
    }

    public boolean isDefined(final String symbol) {
        checkNotNull(symbol);
        return (currentFrame.eval(symbol) != null);
    }

    public void define(final String symbol, final Object value) {
        checkNotNull(symbol);
        checkNotNull(value);
        currentFrame.define(symbol, value);
    }

    public Object eval(final String symbol) {
        checkNotNull(symbol);
        final Object value = currentFrame.eval(symbol);
        checkArgument(value != null, "Symbol \"" + symbol + "\" is undefined");
        return value;
    }

    public Object compute(
            final String symbol, final Function<? super String, ? extends Object> mapping) {
        checkNotNull(symbol);
        checkNotNull(mapping);
        Object value = currentFrame.eval(symbol);
        if (value == null) {
            value = mapping.apply(symbol);
            checkArgument(value != null);
            currentFrame.define(symbol, value);
        }
        return value;
    }

    private static final class Frame {

        private final Frame parent;
        private final Map<String, Object> symbolToValue;

        private Frame(final Frame parent) {
            this.parent = parent;
            symbolToValue = Containers.createMap();
        }

        public void define(final String symbol, final Object value) {
            checkArgument(
                    !symbolToValue.containsKey(symbol),
                    "Symbol   \"" + symbol + "\" is already defined");
            symbolToValue.put(symbol, value);
        }

        public Object eval(final String symbol) {
            final Object value = symbolToValue.get(symbol);
            if (value != null) {
                return value;
            } else if (parent == null) {
                return null;
            } else {
                return parent.eval(symbol);
            }
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(getClass().getSimpleName())
                    .aligned()
                    .addAll(
                            symbolToValue.entrySet().stream()
                                    .map(e -> String.format("(%s %s)", e.getKey(), e.getValue())))
                    .toString();
        }
    }
}
