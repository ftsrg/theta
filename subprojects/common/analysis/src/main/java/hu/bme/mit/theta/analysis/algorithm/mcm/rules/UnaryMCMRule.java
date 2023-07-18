/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm.rules;

import hu.bme.mit.theta.analysis.algorithm.mcm.MCMRelation;
import hu.bme.mit.theta.analysis.algorithm.mcm.MCMRule;

import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public abstract class UnaryMCMRule extends MCMRule {
    protected final MCMRelation e;

    protected UnaryMCMRule(MCMRelation e) {
        this.e = checkNotNull(e);
    }

    @Override
    public void collectRelations(final Map<String, MCMRelation> relations) {
        e.collectRelations(relations);
    }
}
