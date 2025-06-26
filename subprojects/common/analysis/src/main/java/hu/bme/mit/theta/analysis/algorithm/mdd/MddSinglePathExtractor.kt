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
package hu.bme.mit.theta.analysis.algorithm.mdd

import com.google.common.base.Preconditions
import hu.bme.mit.delta.java.mdd.JavaMddFactory
import hu.bme.mit.delta.java.mdd.MddHandle
import hu.bme.mit.delta.java.mdd.impl.MddStructuralTemplate

object MddSinglePathExtractor {

  fun transform(node: MddHandle): MddHandle {

    if (node.isTerminal) {
      Preconditions.checkState(!node.isTerminalZero)
      return node
    } else {

      val templateBuilder = JavaMddFactory.getDefault().createUnsafeTemplateBuilder()

      if (!node.defaultValue().isTerminalZero) {
        templateBuilder.set(0, transform(node.defaultValue()).node)
      } else {
        val cursor = node.cursor()
        cursor.moveNext()
        templateBuilder.set(cursor.key(), transform(cursor.value()).node)
      }

      return node.variableHandle.checkInNode(
        MddStructuralTemplate.of(templateBuilder.buildAndReset())
      )
    }
  }
}
