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
package hu.bme.mit.theta.core.type.anytype;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

public class InvalidLitExpr<ExprType extends Type> extends NullaryExpr<ExprType>
        implements LitExpr<ExprType> {

    private final ExprType type;

    public InvalidLitExpr(ExprType type) {
        this.type = Preconditions.checkNotNull(type);
    }

    @Override
    public ExprType getType() {
        return type;
    }

    @Override
    public LitExpr<ExprType> eval(Valuation val) {
        return this;
    }

    @Override
    public boolean isInvalid() {
        return true;
    }

    @Override
    public boolean equals(Object obj) {
        return false;
    }
}
