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
package hu.bme.mit.theta.xcfa

/**
 * Represents the property to be verified on an XCFA model.
 *
 * The `inputProperty` is the original property specified by the user. The `verifiedProperty` is the
 * (potentially transformed) property being verified on the model.
 *
 * Verifying the `verifiedProperty` on the model should yield equivalent results to verifying the
 * `inputProperty` on the original input task.
 */
class XcfaProperty(val inputProperty: ErrorDetection) {
  var verifiedProperty: ErrorDetection = inputProperty
    private set

  fun transformSpecification(newProperty: ErrorDetection) {
    verifiedProperty = newProperty
  }
}

enum class ErrorDetection {
  ERROR_LOCATION,
  DATA_RACE,
  OVERFLOW,
  MEMSAFETY,
  MEMCLEANUP,
  NO_ERROR,
  TERMINATION,
}
