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
package hu.bme.mit.theta.solver.smtlib.impl.mathsat;

import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibExprTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;

public class MathSATSmtLibExprTransformer extends GenericSmtLibExprTransformer {

    public MathSATSmtLibExprTransformer(final SmtLibTransformationManager transformer) {
        super(transformer);
    }

    @Override
    protected String transformIntRem(final IntRemExpr expr) {
        return String.format("(ite (< %2$s 0) (- (mod %1$s %2$s)) (mod %1$s %2$s))",
                toTerm(expr.getLeftOp()), toTerm(expr.getRightOp()));
    }
}
