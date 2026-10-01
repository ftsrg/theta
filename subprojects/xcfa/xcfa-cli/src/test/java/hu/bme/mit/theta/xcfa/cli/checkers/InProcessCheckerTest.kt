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
package hu.bme.mit.theta.xcfa.cli.checkers

import java.io.File
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.io.TempDir

class InProcessCheckerTest {

  @Test
  fun `the child's folder is created under an output directory that does not exist yet`(
    @TempDir root: File
  ) {
    val resultFolder = root.resolve("not/yet/there")
    val childFolder = createChildResultFolder(resultFolder).toFile()
    assertTrue(childFolder.isDirectory)
    assertEquals(resultFolder.canonicalFile, childFolder.parentFile.canonicalFile)
  }
}
