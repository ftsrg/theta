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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement
import hu.bme.mit.theta.xcfa.model.*
import kotlin.math.max
import kotlin.math.min

data class CMetaData(
  val lineNumberStart: Int?,
  val colNumberStart: Int?,
  val lineNumberStop: Int?,
  val colNumberStop: Int?,
  val offsetStart: Int?,
  val offsetEnd: Int?,
  val sourceText: String?,
  val astNodes: List<CStatement>,
) : MetaData() {

  // AST nodes must be in order of combination!
  override fun combine(other: MetaData): MetaData {
    if (other is CMetaData) {
      return CMetaData(
        lineNumberStart =
          min(
              lineNumberStart ?: other.lineNumberStart ?: -1,
              other.lineNumberStart ?: lineNumberStart ?: -1,
            )
            .takeIf { it > 0 } ?: 0,
        colNumberStart =
          min(
              colNumberStart ?: other.colNumberStart ?: -1,
              other.colNumberStart ?: colNumberStart ?: -1,
            )
            .takeIf { it > 0 } ?: 0,
        offsetStart =
          min(offsetStart ?: other.offsetStart ?: -1, other.offsetStart ?: offsetStart ?: -1)
            .takeIf { it > 0 } ?: 0,
        lineNumberStop =
          max(
              lineNumberStop ?: other.lineNumberStop ?: -1,
              other.lineNumberStop ?: lineNumberStop ?: -1,
            )
            .takeIf { it > 0 } ?: 0,
        colNumberStop =
          max(
              colNumberStop ?: other.colNumberStop ?: -1,
              other.colNumberStop ?: colNumberStop ?: -1,
            )
            .takeIf { it > 0 } ?: 0,
        offsetEnd =
          max(offsetEnd ?: other.offsetEnd ?: -1, other.offsetEnd ?: offsetEnd ?: -1).takeIf {
            it > 0
          } ?: 0,
        sourceText = (sourceText ?: "") + (other.sourceText ?: ""),
        astNodes = astNodes + other.astNodes,
      )
    } else if (other is EmptyMetaData) {
      return this
    } else {
      error("Cannot combine metadata of different types: $this vs $other")
    }
  }
}

fun XcfaLabel.getCMetaData(): CMetaData? {
  return if (this.metadata is CMetaData) {
    this.metadata as CMetaData
  } else {
    null
  }
}

fun XcfaLocation.getCMetaData(): CMetaData? {
  return if (this.metadata is CMetaData) {
    this.metadata as CMetaData
  } else {
    null
  }
}

fun XcfaEdge.getCMetaData(): CMetaData? {
  return if (this.metadata is CMetaData) {
    this.metadata as CMetaData
  } else {
    null
  }
}
