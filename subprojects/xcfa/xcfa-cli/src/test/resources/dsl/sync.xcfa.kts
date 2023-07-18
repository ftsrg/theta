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

import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.xcfa.model.ParamDirection
import hu.bme.mit.theta.xcfa.model.procedure
import hu.bme.mit.theta.xcfa.model.xcfa

xcfa("example") {
    val proc1 = procedure("proc1") {
        val a = "a" type Int() direction ParamDirection.IN
        val b = "b" type Int() direction ParamDirection.OUT

        (init to final) {
            b assign a.ref
        }
    }
    val main = procedure("main") {
        val tmp = "tmp" type Int()
        (init to "L1") {
            proc1("1", tmp.ref)
        }
        ("L1" to final) {
            assume("(= tmp 1)")
        }
        ("L1" to err) {
            assume("(/= tmp 1)")
        }
    }

    main.start()
}