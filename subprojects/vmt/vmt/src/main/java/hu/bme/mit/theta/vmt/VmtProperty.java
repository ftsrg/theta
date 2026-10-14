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
package hu.bme.mit.theta.vmt;

import org.sosy_lab.java_smt.api.BooleanFormula;

/**
 * A property of a VMT model. For {@link Kind#INVARIANT} the formula must hold in every reachable
 * state; for {@link Kind#LIVENESS} it is the VMT {@code :live-property} formula, kept as written.
 */
public record VmtProperty(Kind kind, int index, String name, BooleanFormula formula) {
    public enum Kind {
        INVARIANT,
        LIVENESS
    }
}
