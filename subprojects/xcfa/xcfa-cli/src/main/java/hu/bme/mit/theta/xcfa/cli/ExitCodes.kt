/*
 *  Copyright 2022 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.common.visualization.writer.WebDebuggerLogger
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

fun <T> exitOnError(body: () -> T): T {
    try{
        return body();
    } catch(e: SmtLibSolverException) {
        e.printStackTrace();
        exitProcess(ExitCodes.SOLVER_ERROR.code);
    } catch(e: SolverValidationException) {
        e.printStackTrace();
        exitProcess(ExitCodes.SOLVER_ERROR.code);
    } catch(e: Z3Exception) {
        e.printStackTrace();
        exitProcess(ExitCodes.SOLVER_ERROR.code);
    } catch(e: ClassCastException) {
        e.printStackTrace();
        if (e.message?.contains("com.microsoft.z3") == true)
            exitProcess(ExitCodes.SOLVER_ERROR.code);
        else
            exitProcess(ExitCodes.GENERIC_ERROR.code);
    } catch(e: NotSolvableException) {
        e.printStackTrace();
        exitProcess(ExitCodes.VERIFICATION_STUCK.code);
    } catch(e: OutOfMemoryError) {
        e.printStackTrace();
        exitProcess(ExitCodes.OUT_OF_MEMORY.code);
    } catch (e: RuntimeException) {
        e.printStackTrace();
        exitProcess(ExitCodes.SERVER_ERROR.code);
    } catch(e: Exception) {
        e.printStackTrace();
        exitProcess(ExitCodes.GENERIC_ERROR.code);
    }
}