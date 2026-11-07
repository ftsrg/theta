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
package hu.bme.mit.theta.xcfa.model

abstract class MetaData {

  abstract fun combine(other: MetaData): MetaData

  abstract fun isSubstantial(): Boolean

  /**
   * Called when the visits of a location with this metadata may no longer all pass through
   * locations with this metadata: it was removed, or copied without the marks of [keepsLocation].
   */
  open fun onLocationLost() {}

  /** Whether passes keep a location with this metadata instead of merging it into another. */
  open fun keepsLocation(): Boolean = false

  /**
   * The metadata of a copy of a location with this metadata, without the marks of [keepsLocation].
   */
  open fun withoutLocationMarks(): MetaData = this
}

data object EmptyMetaData : MetaData() {

  override fun combine(other: MetaData): MetaData {
    return other
  }

  override fun isSubstantial(): Boolean {
    return false
  }
}
