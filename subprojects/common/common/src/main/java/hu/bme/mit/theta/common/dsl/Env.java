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
package hu.bme.mit.theta.common.dsl;

import static com.google.common.base.Preconditions.*;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.container.Containers;
import java.util.Map;
import java.util.StringJoiner;
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

    public boolean isDefined(final Symbol symbol) {
        checkNotNull(symbol);
        return (currentFrame.eval(symbol) != null);
    }

    public void define(final Symbol symbol, final Object value) {
        checkNotNull(symbol);
        checkNotNull(value);
        currentFrame.define(symbol, value);
    }

    public Object eval(final Symbol symbol) {
        checkNotNull(symbol);
        final Object value = currentFrame.eval(symbol);
        checkArgument(symbol != null, "Symbol " + symbol.getName() + " is undefined");
        return value;
    }

    @Override
    public String toString() {
        StringJoiner sj = new StringJoiner("\n", "Env( ", " )");
        Frame frame = currentFrame;
        while (frame != null) {
            sj.add(frame.toString());
            frame = frame.parent;
        }
        return sj.toString();
    }

    public <S extends Symbol, V extends Object> Object compute(
            final S symbol, final Function<? super S, ? extends Object> mapping) {
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
        private final Map<Symbol, Object> symbolToValue;

        private Frame(final Frame parent) {
            this.parent = parent;
            symbolToValue = Containers.createMap();
        }

        public void define(final Symbol symbol, final Object value) {
            checkArgument(
                    symbolToValue.get(symbol) == null,
                    "Symbol " + symbol.getName() + " is already defined");
            symbolToValue.put(symbol, value);
        }

        public Object eval(final Symbol symbol) {
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
                    .addAll(
                            symbolToValue.entrySet().stream()
                                    .map(e -> e.getKey().getName() + " <- " + e.getValue())
                                    .collect(toList()))
                    .toString();
        }
    }
}
