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
package hu.bme.mit.theta.core.clock.constr;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;
import java.util.Collection;

public abstract class UnitConstr extends AtomicConstr {

    private final VarDecl<RatType> varDecl;

    private volatile int hashCode = 0;

    protected UnitConstr(final VarDecl<RatType> varDecl, final int bound) {
        super(bound);
        this.varDecl = checkNotNull(varDecl);
    }

    public final VarDecl<RatType> getVar() {
        return varDecl;
    }

    @Override
    public Collection<VarDecl<RatType>> getVars() {
        return ImmutableSet.of(varDecl);
    }

    @Override
    public final int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = getHashSeed();
            result = 31 * result + varDecl.hashCode();
            result = 31 * result + getBound();
            hashCode = result;
        }
        return result;
    }

    @Override
    public final String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append(varDecl.getName());
        sb.append(' ');
        sb.append(getOperatorLabel());
        sb.append(' ');
        sb.append(getBound());
        return sb.toString();
    }

    protected abstract int getHashSeed();

    protected abstract String getOperatorLabel();
}
