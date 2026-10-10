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
package hu.bme.mit.theta.frontend.svlib

import hu.bme.mit.theta.xcfa.model.MetaData

class SvLibTagMetadata(val tags: List<String> = listOf()) : MetaData() {
  override fun combine(other: MetaData) =
    if (other is SvLibTagMetadata) SvLibTagMetadata(this.tags + other.tags) else this

  override fun isSubstantial() = tags.isNotEmpty()
}

class SvLibSourceMetadata(val source: String) : MetaData() {
  override fun combine(other: MetaData) =
    if (other is SvLibSourceMetadata) SvLibSourceMetadata("${this.source} ${other.source}") else this

  override fun isSubstantial() = source.isNotEmpty()
}
