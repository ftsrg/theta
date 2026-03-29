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

package hu.bme.mit.theta.xcfa.witnesses

import java.io.File

class Btor2Witness(private val badProperty: String = "b0") {
  private val frames = mutableMapOf<Int, MutableMap<Int, String>>()

  fun addInput(frameIndex: Int, inputId: Int, value: String) {
    frames.computeIfAbsent(frameIndex) { mutableMapOf() }[inputId] = value
  }

  fun serialize(witnessFile: File) {
    witnessFile.printWriter().use { out ->
      out.println("sat")
      out.println(badProperty)

      for (frame in frames.keys.sorted()) {
        out.println("@$frame")

        val inputs = frames[frame]!!
        for ((id, value) in inputs.entries.sortedBy { it.key }) {
          out.println("$id $value")
        }
      }
      out.println(".")
    }
  }
}
