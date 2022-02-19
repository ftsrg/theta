/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.cat.solver;

public interface RuleDerivationVisitor<P, R> {
	R visit(RuleDerivation.Element derivation, P param);

	R visit(RuleDerivation.Union derivation, P param);

	R visit(RuleDerivation.Intersection derivation, P param);

	R visit(RuleDerivation.Difference derivation, P param);

	R visit(RuleDerivation.Inverse derivation, P param);

	R visit(RuleDerivation.Transitive derivation, P param);

	R visit(RuleDerivation.SelfOrTransitive derivation, P param);

	R visit(RuleDerivation.Consecutive derivation, P param);

	R visit(RuleDerivation.CartesianProduct derivation, P param);
}
