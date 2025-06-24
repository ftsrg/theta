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

package hu.bme.mit.theta.core.type.fptype

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName("FpRoundingMode")
enum class FpRoundingMode {

    RNE, // Round nearest ties to even
    RNA, // Round nearest ties to away
    RTP, // Round toward positive
    RTN, // Round toward negative
    RTZ; // Round toward zero

    companion object {

        @JvmStatic
        val defaultRoundingMode: FpRoundingMode = RNE
    }
}

