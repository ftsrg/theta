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
package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.model.MetaData;
import java.util.List;
import org.jetbrains.annotations.NotNull;

public class ChcMetadata extends MetaData {
    private final String name;
    private final List<VarDecl<?>> varDecls;

    public ChcMetadata(String name, List<VarDecl<?>> varDecls) {
        this.name = name;
        this.varDecls = varDecls;
    }

    @Override
    @NotNull public MetaData combine(@NotNull MetaData other) {
        throw new UnsupportedOperationException("Cannot combine metadata for CHC");
    }

    @Override
    public boolean isSubstantial() {
        return true;
    }

    public String getName() {
        return name;
    }

    public List<VarDecl<?>> getVarDecls() {
        return varDecls;
    }
}
