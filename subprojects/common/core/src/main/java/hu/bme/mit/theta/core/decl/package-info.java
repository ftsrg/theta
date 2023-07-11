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
 * This package contains the different declarations. - {@link hu.bme.mit.theta.core.decl.ConstDecl}
 * represents a constant that can be directly handled by the SMT solvers. -
 * {@link hu.bme.mit.theta.core.decl.VarDecl} represents a variable, that can have multiple
 * associated {@link hu.bme.mit.theta.core.decl.ConstDecl}s for each index (e.g. in a path) -
 * {@link hu.bme.mit.theta.core.decl.ParamDecl} represents a parameter declaration.
 * <p>
 * Use the factory class {@link hu.bme.mit.theta.core.decl.Decls} to instantiate them.
 */

package hu.bme.mit.theta.core.decl;