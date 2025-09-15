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
package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.PartialOrd;

public final class ExplOrd implements PartialOrd<ExplState> {

    private static final class LazyHolder {

        private static final ExplOrd INSTANCE = new ExplOrd();
    }

    private ExplOrd() {}

    public static ExplOrd getInstance() {
        return LazyHolder.INSTANCE;
    }

    @Override
    public boolean isLeq(final ExplState state1, final ExplState state2) {
        return state1.isLeq(state2);
    }
}
