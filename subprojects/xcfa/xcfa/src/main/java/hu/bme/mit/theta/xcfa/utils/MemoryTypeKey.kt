/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.Dereference

/**
 * The memory partition a dereference belongs to: the (array, offset, element) type triple.
 *
 * Every memory representation is partitioned by it -- `DereferenceToArrayPass` keeps one backing
 * array per triple, the OC encoding one memory declaration -- so accesses of different triples
 * never communicate.
 */
data class MemoryTypeKey(val arrayType: Type, val offsetType: Type, val elemType: Type) {

  /** Alphanumeric rendering of the triple, for generated declaration names. */
  val sanitizedName: String
    get() =
      listOf(arrayType, offsetType, elemType).joinToString("_") {
        it.toString().replace(Regex("[^A-Za-z0-9]"), "")
      }
}

val Dereference<*, *, *>.memoryTypeKey: MemoryTypeKey
  get() = MemoryTypeKey(array.type, offset.type, type)
