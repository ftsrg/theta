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
package hu.bme.mit.theta.analysis.multi;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.core.decl.VarDecl;
import java.util.Collection;

@SuppressWarnings("java:S119")
public record MultiPrec<LPrec extends Prec, RPrec extends Prec, DataPrec extends Prec>(
        LPrec leftPrec, RPrec rightPrec, DataPrec dataPrec) implements Prec {

    @Override
    public Collection<VarDecl<?>> getUsedVars() {
        return dataPrec.getUsedVars();
    }

    @Override
    public String toString() {
        return "MultiPrec{" + "dataPrec=" + dataPrec + '}';
    }
}
