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
package hu.bme.mit.theta.common.cfa.buchi.hoa

import java.net.URLEncoder
import java.nio.file.Path

/**
 * Provide a directory which contains HOAF files named as their respective LTL expression .hoa. E.g.
 * if you have the hoaf representation of `F a` as `/tmp/ltls/F a.hoa`, create this class with
 * `/tmp/ltls` and simply call the transform with the ltl expression.
 */
class Ltl2HoafFromDir(private val dir: String) : Ltl2Hoaf {

  override fun transform(ltl: String) =
    Path.of("""$dir/${URLEncoder.encode(ltl, "UTF-8")}.hoa""").toFile().readText()
}
