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
package hu.bme.mit.theta.common.logging

import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.io.File
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger

class LoggerTest {

    @BeforeEach
    fun setup() {
        Logger.close()
    }

    @AfterEach
    fun teardown() {
        Logger.close()
    }

    @Test
    fun `pattern with OR enables only matching types`() {
        Logger.init("DEBUG|INFO")
        assertTrue(Logger.isEnabled(Logger.Level.DEBUG))
        assertTrue(Logger.isEnabled(Logger.Level.INFO))
        assertFalse(Logger.isEnabled(Logger.Level.ERROR))
        assertFalse(Logger.isEnabled(Logger.Level.WARN))
    }

    @Test
    fun `pattern with wildcard enables all types`() {
        Logger.init(".*")
        assertTrue(Logger.isEnabled(Logger.Level.DEBUG))
        assertTrue(Logger.isEnabled(Logger.Level.INFO))
        assertTrue(Logger.isEnabled(Logger.Level.ERROR))
        assertTrue(Logger.isEnabled(Logger.Level.WARN))
        assertTrue(Logger.isEnabled(Logger.Level.RESULT))
    }

    @Test
    fun `pattern is case insensitive`() {
        Logger.init("debug|INFO|WaRn")
        assertTrue(Logger.isEnabled(Logger.Level.DEBUG))
        assertTrue(Logger.isEnabled(Logger.Level.INFO))
        assertTrue(Logger.isEnabled(Logger.Level.WARN))
    }

    @Test
    fun `init throws when already initialized`() {
        Logger.init("DEBUG")
        assertThrows(IllegalStateException::class.java) {
            Logger.init("INFO")
        }
    }

    @Test
    fun `close allows reinitialization`() {
        Logger.init("DEBUG")
        Logger.close()
        assertDoesNotThrow { Logger.init("INFO") }
    }

    @Test
    fun `writes to file when specified`() {
        val tempFile = createTempLogFile()
        Logger.init("INFO", tempFile.absolutePath)
        Logger.info("Hello %s", "World")
        Logger.close()
        val content = tempFile.readText()
        assertTrue(content.contains("Hello World"))
        assertTrue(content.contains("[INFO]"))
    }

    @Test
    fun `writes timestamp in correct format`() {
        val tempFile = createTempLogFile()
        Logger.init("INFO", tempFile.absolutePath)
        Logger.info("Test")
        Logger.close()
        val content = tempFile.readText()
        val timestampRegex = Regex("""\[\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}\]""")
        assertTrue(timestampRegex.containsMatchIn(content))
    }

    @Test
    fun `disabled log type produces no output`() {
        val tempFile = createTempLogFile()
        Logger.init("ERROR", tempFile.absolutePath)
        Logger.info("Should not appear")
        Logger.close()
        val content = tempFile.readText()
        assertFalse(content.contains("Should not appear"))
    }

    @Test
    fun `formats multiple arguments`() {
        val tempFile = createTempLogFile()
        Logger.init("INFO", tempFile.absolutePath)
        Logger.info("String: %s, Int: %d", "test", 42)
        Logger.close()
        val content = tempFile.readText()
        assertTrue(content.contains("String: test"))
        assertTrue(content.contains("Int: 42"))
    }

    @Test
    fun `warnOnce logs only first occurrence`() {
        val tempFile = createTempLogFile()
        Logger.init("WARN", tempFile.absolutePath)
        Logger.warnOnce("Duplicate warning")
        Logger.warnOnce("Duplicate warning")
        Logger.warnOnce("Duplicate warning")
        Logger.close()
        val content = tempFile.readText()
        val count = content.split("Duplicate warning").size - 1
        assertEquals(1, count)
    }

    @Test
    fun `all log types produce correct level markers`() {
        val tempFile = createTempLogFile()
        Logger.init(".*", tempFile.absolutePath)
        Logger.debug("msg")
        Logger.info("msg")
        Logger.warn("msg")
        Logger.error("msg")
        Logger.result("msg")
        Logger.benchmark("msg")
        Logger.mainStep("msg")
        Logger.subStep("msg")
        Logger.detail("msg")
        Logger.verbose("msg")
        Logger.close()
        val content = tempFile.readText()
        assertTrue(content.contains("[DEBUG]"))
        assertTrue(content.contains("[INFO]"))
        assertTrue(content.contains("[WARN]"))
        assertTrue(content.contains("[ERROR]"))
        assertTrue(content.contains("[RESULT]"))
        assertTrue(content.contains("[BENCHMARK]"))
        assertTrue(content.contains("[MAINSTEP]"))
        assertTrue(content.contains("[SUBSTEP]"))
        assertTrue(content.contains("[DETAIL]"))
        assertTrue(content.contains("[VERBOSE]"))
    }

    @Test
    fun `logging without init does not crash`() {
        assertDoesNotThrow {
            Logger.info("Test")
            Logger.debug("Test")
            Logger.warn("Test")
        }
    }

    @Test
    fun `concurrent logging produces all messages`() {
        val tempFile = createTempLogFile()
        Logger.init(".*", tempFile.absolutePath)
        val numThreads = 10
        val messagesPerThread = 50
        val executor = Executors.newFixedThreadPool(numThreads)
        val startLatch = CountDownLatch(1)
        repeat(numThreads) { threadId ->
            executor.submit {
                startLatch.await()
                repeat(messagesPerThread) { msgId ->
                    Logger.info("T%d-M%d", threadId, msgId)
                }
            }
        }
        startLatch.countDown()
        executor.shutdown()
        assertTrue(executor.awaitTermination(30, TimeUnit.SECONDS))
        Logger.close()
        val content = tempFile.readText()
        val actualCount = content.lines().count { it.contains("[INFO]") }
        assertEquals(numThreads * messagesPerThread, actualCount)
    }

    @Test
    fun `concurrent warnOnce is thread safe`() {
        val tempFile = createTempLogFile()
        Logger.init("WARN", tempFile.absolutePath)
        val numThreads = 20
        val executor = Executors.newFixedThreadPool(numThreads)
        val startLatch = CountDownLatch(1)
        repeat(numThreads) {
            executor.submit {
                startLatch.await()
                Logger.warnOnce("Concurrent warning")
            }
        }
        startLatch.countDown()
        executor.shutdown()
        assertTrue(executor.awaitTermination(30, TimeUnit.SECONDS))
        Logger.close()
        val content = tempFile.readText()
        val count = content.split("Concurrent warning").size - 1
        assertEquals(1, count)
    }

    @Test
    fun `concurrent init only succeeds once`() {
        val tempFile = createTempLogFile()
        val numThreads = 10
        val successCount = AtomicInteger(0)
        val failureCount = AtomicInteger(0)
        val startLatch = CountDownLatch(1)
        val threads = (0 until numThreads).map {
            Thread {
                startLatch.await()
                try {
                    Logger.init("DEBUG", tempFile.absolutePath)
                    successCount.incrementAndGet()
                } catch (e: IllegalStateException) {
                    failureCount.incrementAndGet()
                }
            }
        }
        threads.forEach { it.start() }
        startLatch.countDown()
        threads.forEach { it.join() }
        assertEquals(1, successCount.get())
        assertEquals(numThreads - 1, failureCount.get())
    }

    @Test
    fun `concurrent isEnabled is thread safe`() {
        val tempFile = createTempLogFile()
        Logger.init("DEBUG|INFO", tempFile.absolutePath)
        val numThreads = 20
        val iterations = 1000
        val executor = Executors.newFixedThreadPool(numThreads)
        val startLatch = CountDownLatch(1)
        val errors = AtomicInteger(0)
        repeat(numThreads) {
            executor.submit {
                startLatch.await()
                repeat(iterations) {
                    if (!Logger.isEnabled(Logger.Level.DEBUG)) errors.incrementAndGet()
                    if (!Logger.isEnabled(Logger.Level.INFO)) errors.incrementAndGet()
                    if (Logger.isEnabled(Logger.Level.ERROR)) errors.incrementAndGet()
                }
            }
        }
        startLatch.countDown()
        executor.shutdown()
        assertTrue(executor.awaitTermination(30, TimeUnit.SECONDS))
        assertEquals(0, errors.get())
    }

    private fun createTempLogFile(): File {
        val file = File.createTempFile("theta_logger_test_", ".log")
        file.deleteOnExit()
        return file
    }
}
