/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.xcfa.SyntheticType;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Optional;

/**
 * The interface for an ExplicitState and a Transition needed to determine
 * whether the transition is enabled or not.
 */
interface ExplStateReadOnlyInterface {
    /**
     * Returns the value of the variable.
     * @param expr The expression to evaluate
     * @param <DeclType> The type of the variable
     * @return The current value of the expression. If empty, there are havoc'd variables in the statement.
     */
    <DeclType extends Type> Optional<LitExpr<DeclType>> eval(Expr<DeclType> expr);

    /**
     * Returns the process of the transition.
     * @return the process of the transition.
     */
    XCFA.Process getTransitionProcess();
}
