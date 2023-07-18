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

package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer;

import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CInteger extends CComplexType {

    protected int rank;
    protected boolean unsigned = false;

    protected CInteger(CSimpleType origin, ParseContext parseContext) {
        super(origin, parseContext);
    }

    public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
        return visitor.visit(this, param);
    }

    @Override
    public CComplexType getSmallestCommonType(CComplexType type) {
        if (type instanceof CInteger && ((CInteger) type).rank <= rank) {
            if (((CInteger) type).unsigned) {
                if (unsigned || type.width() < width()) {
                    return this;
                } else {
                    return getUnsignedVersion();
                }
            } else {
                return this;
            }
        } else {
            return type.getSmallestCommonType(this);
        }
    }

    public boolean isSsigned() {
        return !unsigned;
    }

    public abstract CInteger getSignedVersion();

    public abstract CInteger getUnsignedVersion();
}
