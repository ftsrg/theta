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
/**
 * This package contains different implementations of models that assign expressions or literals to
 * declarations. - {@link hu.bme.mit.theta.core.model.Substitution} is a substitution that maps
 * expressions to declarations. - {@link hu.bme.mit.theta.core.model.BasicSubstitution} is a basic
 * implementation of a substitution. - {@link hu.bme.mit.theta.core.model.NestedSubstitution}
 * implements a scoped substitution. - {@link hu.bme.mit.theta.core.model.Valuation} is a special
 * case of {@link hu.bme.mit.theta.core.model.Substitution} where literal expressions are assigned
 * to declarations. - {@link hu.bme.mit.theta.core.model.MutableValuation} implements a mutable
 * valuation. - {@link hu.bme.mit.theta.core.model.ImmutableValuation} implements an immutable
 * valuation.
 */

package hu.bme.mit.theta.core.model;