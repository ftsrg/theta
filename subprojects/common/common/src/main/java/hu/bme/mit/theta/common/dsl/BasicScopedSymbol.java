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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;

public final class BasicScopedSymbol implements ScopedSymbol {

    private final String name;
    private final BasicScope scope;

    public BasicScopedSymbol(
            final String name,
            final Scope eclosingScope,
            final Collection<? extends Symbol> symbols) {
        checkNotNull(name);
        checkArgument(name.length() > 0);
        this.name = name;
        scope = new BasicScope(eclosingScope);
    }

    ////

    public void declare(final Symbol symbol) {
        scope.declare(symbol);
    }

    public void declareAll(final Collection<? extends Symbol> symbols) {
        scope.declareAll(symbols);
    }

    ////

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Optional<? extends Symbol> resolve(final String name) {
        return scope.resolve(name);
    }

    @Override
    public Optional<? extends Scope> enclosingScope() {
        return scope.enclosingScope();
    }
}
