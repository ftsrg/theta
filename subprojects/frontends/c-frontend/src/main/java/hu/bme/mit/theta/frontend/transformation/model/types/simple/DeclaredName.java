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

package hu.bme.mit.theta.frontend.transformation.model.types.simple;

public class DeclaredName extends CSimpleType {

    private String declaredName;

    DeclaredName(String declaredName) {
        this.declaredName = declaredName;
    }

    @Override
    protected void patch(CSimpleType cSimpleType) {
        cSimpleType.setAssociatedName(declaredName);
    }

    @Override
    public CSimpleType copyOf() {
        CSimpleType declaredNameRet = new DeclaredName(declaredName);
        declaredNameRet.setAtomic(this.isAtomic());
        declaredNameRet.setExtern(this.isExtern());
        declaredNameRet.setTypedef(this.isTypedef());
        declaredNameRet.setVolatile(this.isVolatile());
        declaredNameRet.setSigned(this.isSigned());
        declaredNameRet.setShort(this.isShort());
        declaredNameRet.setLong(this.isLong());
        declaredNameRet.setBool(this.isBool());
        declaredNameRet.setLongLong(this.isLongLong());
        declaredNameRet.set128(this.is128());
        for (int i = 0; i < this.getPointerLevel(); i++) {
            declaredNameRet.incrementPointer();
        }

        return declaredNameRet;
    }

    public String getDeclaredName() {
        return declaredName;
    }
}
