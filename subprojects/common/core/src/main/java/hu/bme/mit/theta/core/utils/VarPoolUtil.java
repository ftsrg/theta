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
package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.ArrayDeque;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class VarPoolUtil {

    private VarPoolUtil() {
    }

    private final static ArrayDeque<VarDecl<IntType>> intPool = new ArrayDeque<VarDecl<IntType>>();
    private static int counter = 0;

    public static VarDecl<IntType> requestInt() {
        if (intPool.isEmpty()) {
            return Decls.Var("temp" + counter++, Int());
        } else {
            return intPool.remove();
        }
    }

    public static void returnInt(VarDecl<IntType> var) {
        if (!intPool.contains(var)) {
            intPool.addFirst(var);
        }
    }

}
