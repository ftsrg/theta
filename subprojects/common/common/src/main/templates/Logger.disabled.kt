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
@file:Suppress("unused")

package hu.bme.mit.theta.common.logging

object Logger {

    const val ALL = "ERROR|WARN|RESULT|BENCHMARK|MAINSTEP|SUBSTEP|INFO|DETAIL|VERBOSE|DEBUG_SOLVER"

    @JvmStatic
    fun init(pattern: String, file: String?) {}

    @JvmStatic
    fun init(pattern: String) {}

    @JvmStatic
    fun debug(format: String, vararg args: Any?) {}

    @JvmStatic
    fun solverDebug(format: String, vararg args: Any?) {}

    @JvmStatic
    fun info(format: String, vararg args: Any?) {}

    @JvmStatic
    fun warn(format: String, vararg args: Any?) {}

    @JvmStatic
    fun error(format: String, vararg args: Any?) {}

    @JvmStatic
    fun warnOnce(format: String, vararg args: Any?) {}

    @JvmStatic
    fun infoOnce(format: String, vararg args: Any?) {}

    @JvmStatic
    fun errorOnce(format: String, vararg args: Any?) {}

    @JvmStatic
    fun result(format: String, vararg args: Any?) {}

    @JvmStatic
    fun benchmark(format: String, vararg args: Any?) {}

    @JvmStatic
    fun mainStep(format: String, vararg args: Any?) {}

    @JvmStatic
    fun subStep(format: String, vararg args: Any?) {}

    @JvmStatic
    fun detail(format: String, vararg args: Any?) {}

    @JvmStatic
    fun verbose(format: String, vararg args: Any?) {}

    @JvmStatic
    fun isEnabled(type: String): Boolean = false

    @JvmStatic
    fun close() {}
}
