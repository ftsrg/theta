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
package hu.bme.mit.theta.xcfa.analysis

import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddExpressionRepresentation
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.logging.NullLogger
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.solver.SolverPool
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xcfa.ErrorDetection
import hu.bme.mit.theta.xcfa.XcfaProperty
import hu.bme.mit.theta.xcfa.analysis.monolithic.XcfaMultiThreadToMonolithicAdapter
import hu.bme.mit.theta.xcfa.passes.DereferenceToArrayPass
import hu.bme.mit.theta.xcfa.passes.LbePass
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource

class SymbolicMutexDataRaceTest {
  @ParameterizedTest
  @CsvSource(
    "p->datum++,true",
    "a[i].datum++,true",
    "i++; p->datum++,true",
    "i=1-i; a[i].datum++,false",
  )
  fun mutexAndDataAtTheSameIndex(access: String, safe: Boolean) {
    val program =
      """
      #include <pthread.h>
      extern int __VERIFIER_nondet_int(void);
      extern void abort(void);
      struct cell { int datum; pthread_mutex_t mutex; } a[2];
      void *worker(void *arg) {
        int i = __VERIFIER_nondet_int();
        if (i < 0 || i >= 2) abort();
        struct cell *p = &a[i];
        pthread_mutex_lock(&p->mutex);
        $access;
        pthread_mutex_unlock(&p->mutex);
        return 0;
      }
      int main(void) {
        for (int j = 0; j < 2; j++) pthread_mutex_init(&a[j].mutex, 0);
        int i = __VERIFIER_nondet_int();
        if (i < 0 || i >= 2) abort();
        pthread_t thread;
        pthread_create(&thread, 0, worker, 0);
        pthread_mutex_lock(&a[i].mutex);
        a[i].datum++;
        pthread_mutex_unlock(&a[i].mutex);
        return 0;
      }
      """
        .trimIndent()
    val property = XcfaProperty(ErrorDetection.DATA_RACE)
    val context = ParseContext().apply { isCheckDataRace = true }
    val level = LbePass.defaultLevel
    val xcfa =
      try {
        LbePass.defaultLevel = LbePass.LbeLevel.LBE_LOCAL
        getXcfaFromC(program.byteInputStream(), context, false, property, NullLogger.getInstance())
          .first
      } finally {
        LbePass.defaultLevel = level
      }
    val zeroInitialized = DereferenceToArrayPass.zeroInitialized
    val monolithic =
      try {
        DereferenceToArrayPass.zeroInitialized = true
        XcfaMultiThreadToMonolithicAdapter(xcfa, property, context, true).monolithicExpr
      } finally {
        DereferenceToArrayPass.zeroInitialized = zeroInitialized
      }
    SolverPool(Z3SolverFactory.getInstance()).use { pool ->
      val result =
        MddChecker(
            monolithic,
            pool,
            NullLogger.getInstance(),
            lookAheadStrategy = MddExpressionRepresentation.MddToExprStrategy.NODE_LEVEL,
          )
          .check(null)
      assertEquals(safe, result.isSafe)
      assertEquals(!safe, result.isUnsafe)
    }
  }
}
