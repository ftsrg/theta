/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.ic3;

public class CarOptimizations extends BaseOptimizations {

    private final boolean coverOpt;

    public CarOptimizations(
            boolean unSatOpt,
            boolean notBOpt,
            boolean propagateOpt,
            boolean propertyOpt,
            boolean filterOpt,
            boolean generalizeOpt,
            boolean unsatPropagateOpt,
            boolean coverOpt) {
        super(
                unSatOpt,
                notBOpt,
                propagateOpt,
                filterOpt,
                propertyOpt,
                generalizeOpt,
                unsatPropagateOpt);
        this.coverOpt = coverOpt;
    }

    public boolean isCoverOpt() {
        return coverOpt;
    }
}
