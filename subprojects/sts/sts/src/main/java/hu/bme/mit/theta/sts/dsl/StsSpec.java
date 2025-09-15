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
package hu.bme.mit.theta.sts.dsl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import hu.bme.mit.theta.common.dsl.Symbol;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.sts.STS;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

public final class StsSpec {

    private final StsSpecSymbol stsSpecSymbol;
    private final Substitution assignment;

    private StsSpec(final StsSpecSymbol stsSpecSymbol, final Substitution assignment) {
        this.stsSpecSymbol = checkNotNull(stsSpecSymbol);
        this.assignment = checkNotNull(assignment);
    }

    static StsSpec create(final StsSpecSymbol stsSpecSymbol, final Substitution assignment) {
        return new StsSpec(stsSpecSymbol, assignment);
    }

    ////

    public Collection<STS> getAllSts() {
        return stsSpecSymbol.getPropDeclSymbols().stream()
                .map(s -> s.instantiate(assignment))
                .collect(toList());
    }

    ////

    public STS createSts(final String name, final Expr<?>... args) {
        return createSts(name, Arrays.asList(args));
    }

    public STS createSts(final String name, final List<? extends Expr<?>> args) {
        final StsDeclSymbol stsDeclSymbol = resolveStsDeclSymbol(name);
        final StsDefScope stsDefScope = stsDeclSymbol.instantiate(assignment, args);
        final STS sts = stsDefScope.getSts();
        return sts;
    }

    private StsDeclSymbol resolveStsDeclSymbol(final String name) {
        final Optional<Symbol> optSymbol = stsSpecSymbol.resolve(name);
        checkArgument(optSymbol.isPresent());
        final Symbol symbol = optSymbol.get();
        checkArgument(symbol instanceof StsDeclSymbol);
        final StsDeclSymbol stsDeclSymbol = (StsDeclSymbol) symbol;
        return stsDeclSymbol;
    }

    ////

    public STS createProp(final String name) {
        final PropDeclSymbol propDeclSymbol = resolvePropDeclSymbol(name);
        final STS sts = propDeclSymbol.instantiate(assignment);
        return sts;
    }

    private PropDeclSymbol resolvePropDeclSymbol(final String name) {
        final Optional<Symbol> optSymbol = stsSpecSymbol.resolve(name);
        checkArgument(optSymbol.isPresent(), "Property not found");
        final Symbol symbol = optSymbol.get();
        checkArgument(symbol instanceof PropDeclSymbol);
        final PropDeclSymbol propDeclSymbol = (PropDeclSymbol) symbol;
        return propDeclSymbol;
    }
}
