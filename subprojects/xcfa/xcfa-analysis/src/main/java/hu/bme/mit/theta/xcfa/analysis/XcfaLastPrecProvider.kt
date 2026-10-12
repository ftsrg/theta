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
package hu.bme.mit.theta.xcfa.analysis

/**
 * A checker that can tell which precision its last check ended with - for CEGAR, the precision
 * after the last refinement. Checkers without a precision of their own (e.g. bounded model
 * checkers) do not implement it.
 */
interface XcfaLastPrecProvider {
  val lastPrec: XcfaPrec<*>?
}
