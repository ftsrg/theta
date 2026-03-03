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

import java.io.File
import java.io.FileWriter
import java.io.PrintWriter
import java.io.Writer
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.util.concurrent.locks.ReentrantReadWriteLock
import kotlin.concurrent.withLock

object Logger {

    private val logTypes = mapOf(
        "debug" to "DEBUG",
        "info" to "INFO",
        "warning" to "WARN",
        "warn" to "WARN",
        "error" to "ERROR",
        "result" to "RESULT",
        "benchmark" to "BENCHMARK",
        "mainstep" to "MAINSTEP",
        "substep" to "SUBSTEP",
        "detail" to "DETAIL",
        "verbose" to "VERBOSE",
        "genericsolver" to "DEBUG_GENERICSOLVER",
        "yicesolver" to "DEBUG_YICESSOLVER"
    )

    private val enabled = mutableSetOf<String>()
    private var output: Writer = System.err.writer()
    private val loggedOnceMessages = mutableSetOf<String>()
    private var initialized = false
    private val timestampFormat = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss")
    private val lock = ReentrantReadWriteLock()

    private fun logBeforeInit(level: String, message: String) {
        val timestamp = LocalDateTime.now().format(timestampFormat)
        val stackTrace = Thread.currentThread().stackTrace
        val caller = stackTrace.find { it.className == "hu.bme.mit.theta.common.logging.Logger" && it.methodName != "logBeforeInit" }
        val fileName = caller?.fileName ?: "Unknown"
        val lineNumber = caller?.lineNumber ?: -1
        val methodName = caller?.methodName ?: "unknown"
        val context = if (level == "ERROR") " - Check pattern format, file permissions, or file path" else ""
        System.err.println("[$timestamp] [$level] $fileName:$lineNumber Logger.$methodName: $message$context")
    }

    @JvmStatic
    fun init(pattern: String, file: String?) {
        lock.writeLock().withLock {
            if (initialized) {
                logBeforeInit("ERROR", "Logger already initialized")
                throw IllegalStateException("Logger already initialized")
            }

            if (file != null && file.isNotEmpty()) {
                try {
                    val logFile = File(file)
                    output = PrintWriter(FileWriter(logFile, true), true)
                    logBeforeInit("INFO", "Logging to file: $file")
                } catch (e: Exception) {
                    logBeforeInit("ERROR", "Failed to open log file: ${e.message}")
                    throw e
                }
            } else {
                logBeforeInit("INFO", "Logging to stderr")
            }

            val regex = pattern.toRegex(RegexOption.IGNORE_CASE)
            logTypes.values.forEach { type ->
                if (regex.containsMatchIn(type)) {
                    enabled.add(type)
                }
            }

            if (enabled.isEmpty()) {
                logBeforeInit("WARN", "No log types matched pattern: $pattern")
            } else {
                logBeforeInit("INFO", "Enabled log types: ${enabled.joinToString(", ")}")
            }

            initialized = true
        }
    }

    @JvmStatic
    fun init(pattern: String) = init(pattern, null)

    private fun requireInit(): Boolean {
        lock.readLock().withLock { 
            if(!initialized) {
              logBeforeInit("ERROR", "Logger not initialized")
            }
            return initialized
        }
    }

    private fun getLocation(): String {
        val stackTrace = Thread.currentThread().stackTrace
        val caller = stackTrace.asSequence()
            .dropWhile { 
                it.className.startsWith("hu.bme.mit.theta.common.logging.Logger") ||
                it.className.startsWith("java.") ||
                it.className.startsWith("jdk.") ||
                it.className.startsWith("sun.") ||
                it.className.startsWith("kotlin.") ||
                it.className.startsWith("kotlinx.") ||
                it.className.startsWith("org.junit.")
            }
            .firstOrNull()
        val fileName = caller?.fileName ?: "Unknown"
        val lineNumber = caller?.lineNumber ?: -1
        return "$fileName:$lineNumber"
    }

    private fun formatMessage(level: String, location: String, message: String): String {
        val timestamp = LocalDateTime.now().format(timestampFormat)
        return "[$timestamp] [$level] $location $message"
    }

    private fun log(level: String, format: String, vararg args: Any?) {
        val shouldLog = lock.readLock().withLock {
            enabled.contains(level)
        }
        if (!shouldLog) return
        val location = getLocation()
        val message = String.format(format, *args)
        val formatted = formatMessage(level, location, message)
        lock.writeLock().withLock {
            output.write(formatted)
            output.write("\n")
            output.flush()
        }
    }

    @JvmStatic
    fun debug(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("DEBUG", format, *args)
    }

    @JvmStatic
    fun genericsolver(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("DEBUG_GENERICSOLVER", format, *args)
    }

    @JvmStatic
    fun yicesolver(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("DEBUG_YICESSOLVER", format, *args)
    }

    @JvmStatic
    fun info(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("INFO", format, *args)
    }

    @JvmStatic
    fun warn(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("WARN", format, *args)
    }

    @JvmStatic
    fun error(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("ERROR", format, *args)
    }

    @JvmStatic
    fun warnOnce(format: String, vararg args: Any?) {
        if (!requireInit()) return
        val message = String.format(format, *args)
        val isNew = lock.writeLock().withLock {
            if (loggedOnceMessages.contains(message)) false
            else {
                loggedOnceMessages.add(message)
                true
            }
        }
        if (isNew) warn(format, *args)
    }

    @JvmStatic
    fun infoOnce(format: String, vararg args: Any?) {
        if (!requireInit()) return
        val message = String.format(format, *args)
        val isNew = lock.writeLock().withLock {
            if (loggedOnceMessages.contains(message)) false
            else {
                loggedOnceMessages.add(message)
                true
            }
        }
        if (isNew) info(format, *args)
    }

    @JvmStatic
    fun result(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("RESULT", format, *args)
    }

    @JvmStatic
    fun benchmark(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("BENCHMARK", format, *args)
    }

    @JvmStatic
    fun mainStep(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("MAINSTEP", format, *args)
    }

    @JvmStatic
    fun subStep(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("SUBSTEP", format, *args)
    }

    @JvmStatic
    fun detail(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("DETAIL", format, *args)
    }

    @JvmStatic
    fun verbose(format: String, vararg args: Any?) {
        if (!requireInit()) return
        log("VERBOSE", format, *args)
    }

    @JvmStatic
    fun isEnabled(type: String): Boolean {
        val normalizedType = type.lowercase().trim()
        return lock.readLock().withLock {
            enabled.contains(logTypes[normalizedType])
        }
    }

    @JvmStatic
    fun write(level: Level, format: String, vararg args: Any?) {
        when (level) {
            Level.VERBOSE -> verbose(format, *args)
            Level.DETAIL -> detail(format, *args)
            Level.INFO -> info(format, *args)
            Level.SUBSTEP -> subStep(format, *args)
            Level.MAINSTEP -> mainStep(format, *args)
            Level.BENCHMARK -> benchmark(format, *args)
            Level.RESULT -> result(format, *args)
            Level.DISABLE -> { /* do nothing */ }
        }
    }

    @JvmStatic
    fun writeln(level: Level, format: String, vararg args: Any?) {
        write(level, format + "%n", *args)
    }

    @JvmStatic
    fun write(level: LegacyLevel, format: String, vararg args: Any?) {
        write(Level.valueOf(level.name), format, *args)
    }

    @JvmStatic
    fun writeln(level: LegacyLevel, format: String, vararg args: Any?) {
        writeln(Level.valueOf(level.name), format, *args)
    }

    @JvmStatic
    fun close() {
        lock.writeLock().withLock {
            try {
                output.close()
                logBeforeInit("INFO", "Logger closed")
            } catch (e: Exception) {
                logBeforeInit("ERROR", "Failed to close logger: ${e.message}")
            } finally {
                initialized = false
                enabled.clear()
                loggedOnceMessages.clear()
            }
        }
    }

    @JvmStatic
    internal fun resetForTest() {
        lock.writeLock().withLock {
            enabled.clear()
            loggedOnceMessages.clear()
            initialized = false
        }
    }

    @Deprecated("Use LegacyLevel instead", ReplaceWith("LegacyLevel"))
    enum class Level {
        DISABLE,
        RESULT,
        BENCHMARK,
        MAINSTEP,
        SUBSTEP,
        INFO,
        DETAIL,
        VERBOSE
    }

    enum class LegacyLevel {
        DISABLE,   
        RESULT,    
        BENCHMARK, 
        MAINSTEP,  
        SUBSTEP,   
        INFO,      
        DETAIL,    
        VERBOSE    
    }

    @JvmStatic
    @JvmOverloads
    fun initOld(level: LegacyLevel, file: String? = null) {
        try {
            if (level == LegacyLevel.DISABLE) {
                init("DISABLED_MATCH_NONE", file)
                return
            }

            // INFO: We assume ERROR and WARN should always be printed if logging is NOT disabled
            val enabledLevels = mutableListOf("ERROR", "WARN")

            for (l in LegacyLevel.values()) {
                if (l == LegacyLevel.DISABLE) continue
                if (l.ordinal <= level.ordinal) {
                    enabledLevels.add(l.name)
                }
            }

            val pattern = enabledLevels.joinToString("|")

            init(pattern, file)
        } catch (e: IllegalStateException) {
            // Idempotent: already initialized, that's fine
            if (e.message?.contains("already initialized") == true) {
                return
            }
            throw e
        }
    }

}
