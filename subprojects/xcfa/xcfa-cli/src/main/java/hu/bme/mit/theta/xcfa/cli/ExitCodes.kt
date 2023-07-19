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

package hu.bme.mit.theta.xcfa.cli

import com.microsoft.z3.Z3Exception
import hu.bme.mit.theta.common.exception.NotSolvableException
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException
import hu.bme.mit.theta.solver.validator.SolverValidationException
import kotlin.system.exitProcess


enum class ExitCodes(val code: Int) {
    GENERIC_ERROR(1),
    OUT_OF_MEMORY(200),
    TIMEOUT(201),
    SERVER_ERROR(202),
    PORTFOLIO_ERROR(203),

    FRONTEND_FAILED(210),
    INVALID_PARAM(211),

    VERIFICATION_STUCK(220),
    SOLVER_ERROR(221),
}

data class ErrorCodeException(val code: Int) : Exception()

private fun exitProcess(debug: Boolean, e: Throwable, code: Int): Nothing {
    if (debug) {
        throw ErrorCodeException(code)
    } else exitProcess(code)
}


fun <T> exitOnError(stacktrace: Boolean, debug: Boolean, body: () -> T): T {
    try {
        return body()
    } catch (e: SmtLibSolverException) {
        if (stacktrace) e.printStackTrace();
        exitProcess(debug, e, ExitCodes.SOLVER_ERROR.code)
    } catch (e: SolverValidationException) {
        if (stacktrace) e.printStackTrace();
        exitProcess(debug, e, ExitCodes.SOLVER_ERROR.code);
    } catch (e: Z3Exception) {
        if (stacktrace) e.printStackTrace();
        exitProcess(debug, e, ExitCodes.SOLVER_ERROR.code);
    } catch (e: ClassCastException) {
        if (stacktrace) e.printStackTrace();
        if (e.message?.contains("com.microsoft.z3") == true)
            exitProcess(debug, e, ExitCodes.SOLVER_ERROR.code);
        else
            exitProcess(debug, e, ExitCodes.GENERIC_ERROR.code);
    } catch (e: NotSolvableException) {
        if (stacktrace) e.printStackTrace();
        exitProcess(debug, e, ExitCodes.VERIFICATION_STUCK.code);
    } catch (e: OutOfMemoryError) {
        if (stacktrace) e.printStackTrace();
        exitProcess(debug, e, ExitCodes.OUT_OF_MEMORY.code);
    } catch (e: RuntimeException) {
        if (stacktrace) e.printStackTrace();
        exitProcess(debug, e, ExitCodes.SERVER_ERROR.code);
    } catch (e: Exception) {
        if (stacktrace) e.printStackTrace();
        exitProcess(debug, e, ExitCodes.GENERIC_ERROR.code);
    }
}