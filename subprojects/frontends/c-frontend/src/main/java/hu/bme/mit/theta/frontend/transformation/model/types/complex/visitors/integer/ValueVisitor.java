/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class ValueVisitor extends CComplexType.CComplexTypeVisitor<String, LitExpr<?>> {

    public static final ValueVisitor instance = new ValueVisitor();

    @Override
    public LitExpr<?> visit(CInteger type, String param) {
        return Int(new BigInteger(param));
    }

}
