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
package hu.bme.mit.theta.core.serialization

import java.security.MessageDigest
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.descriptors.SerialDescriptor

/**
 * A hash of the shapes of [descriptors]: class and element names, kinds, nullability and
 * optionality, recursively. A writer stamps its output with it, so that a reader built with a
 * different shape of any of these classes refuses the output instead of misreading it.
 */
@OptIn(ExperimentalSerializationApi::class)
fun formatFingerprint(descriptors: Collection<SerialDescriptor>): String {
  val text = StringBuilder()
  val seen = HashSet<String>()
  fun describe(d: SerialDescriptor) {
    text.append(d.serialName).append('|').append(d.kind).append(if (d.isNullable) "?" else "")
    // Recursive classes are described once; later mentions are by name.
    if (!seen.add("${d.serialName}|${d.kind}|${d.isNullable}")) return
    text.append('(')
    for (i in 0 until d.elementsCount) {
      text.append(d.getElementName(i)).append(if (d.isElementOptional(i)) "=" else "").append(':')
      describe(d.getElementDescriptor(i))
      text.append(',')
    }
    text.append(')')
  }
  descriptors
    .sortedBy { it.serialName }
    .forEach {
      describe(it)
      text.append('\n')
    }
  val digest = MessageDigest.getInstance("SHA-256").digest(text.toString().toByteArray())
  return digest.take(12).joinToString("") { "%02x".format(it) }
}
