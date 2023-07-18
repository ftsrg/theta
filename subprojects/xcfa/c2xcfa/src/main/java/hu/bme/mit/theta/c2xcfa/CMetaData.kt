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
package hu.bme.mit.theta.c2xcfa

import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaLocation

data class CMetaData(
    val lineNumberStart: Int?,
    val colNumberStart: Int?,
    val lineNumberStop: Int?,
    val colNumberStop: Int?,
    val offsetStart: Int?,
    val offsetEnd: Int?,
    val sourceText: String?
) : MetaData()

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