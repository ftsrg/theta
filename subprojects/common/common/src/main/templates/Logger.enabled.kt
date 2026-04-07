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
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.withLock

object Logger {

    const val ALL: String = "ERROR|WARN|RESULT|BENCHMARK|MAINSTEP|SUBSTEP|INFO|DETAIL|VERBOSE|DEBUG_SOLVER"

    enum class Level(val canonicalName: String) {
        DEBUG("DEBUG"),
        INFO("INFO"),
        WARN("WARN"),
        ERROR("ERROR"),
        RESULT("RESULT"),
        BENCHMARK("BENCHMARK"),
        MAINSTEP("MAINSTEP"),
        SUBSTEP("SUBSTEP"),
        DETAIL("DETAIL"),
        VERBOSE("VERBOSE"),
        DEBUG_SOLVER("DEBUG_SOLVER");

        companion object {
            private val byCanonicalName: Map<String, Level> = entries.associateBy { level: Level -> level.canonicalName }
            fun fromCanonicalName(name: String): Level? = byCanonicalName[name]
        }
    }

    private val enabled: BooleanArray = BooleanArray(Level.entries.size)
    @Volatile
    private var initialized: Boolean = false
    private val writeLock: ReentrantLock = ReentrantLock()
    private var output: Writer = System.err.writer()
    private val loggedOnceMessages: MutableSet<String> = mutableSetOf<String>()
    private val timestampFormat: DateTimeFormatter = DateTimeFormatter.ofPattern("yyyy-MM-dd HH:mm:ss")

    private fun logBeforeInit(level: String, message: String): Unit {
        val timestamp: String = LocalDateTime.now().format(timestampFormat)
        val stackTrace: Array<StackTraceElement> = Thread.currentThread().stackTrace
        val caller: StackTraceElement? = stackTrace.find { element: StackTraceElement ->
            element.className == "hu.bme.mit.theta.common.logging.Logger" && element.methodName != "logBeforeInit"
        }
        val fileName: String = caller?.fileName ?: "Unknown"
        val lineNumber: Int = caller?.lineNumber ?: -1
        val methodName: String = caller?.methodName ?: "unknown"
        val context: String = if (level == "ERROR") " - Check pattern format, file permissions, or file path" else ""
        System.err.println("[$timestamp] [$level] $fileName:$lineNumber Logger.$methodName: $message$context")
    }

    @JvmStatic
    fun init(pattern: String, file: String?): Unit {
        writeLock.withLock {
            if (initialized) {
                logBeforeInit("ERROR", "Logger already initialized")
                throw IllegalStateException("Logger already initialized")
            }

            if (file != null && file.isNotEmpty()) {
                try {
                    val logFile: File = File(file)
                    output = PrintWriter(FileWriter(logFile, true), true)
                    logBeforeInit("INFO", "Logging to file: $file")
                } catch (e: Exception) {
                    logBeforeInit("ERROR", "Failed to open log file: ${e.message}")
                    throw e
                }
            } else {
                logBeforeInit("INFO", "Logging to stderr")
            }

            val regex: Regex = pattern.toRegex(RegexOption.IGNORE_CASE)
            for (level: Level in Level.entries) {
                if (regex.containsMatchIn(level.canonicalName)) {
                    enabled[level.ordinal] = true
                }
            }

            if (!enabled.any()) {
                logBeforeInit("WARN", "No log types matched pattern: $pattern")
            } else {
                logBeforeInit("INFO", "Enabled log types: ${Level.entries.filter { level: Level -> enabled[level.ordinal] }.joinToString(", ") { level: Level -> level.canonicalName }}")
            }

            initialized = true
        }
    }

    @JvmStatic
    fun init(pattern: String): Unit = init(pattern, null)

    private fun requireInit(): Boolean {
        if (initialized) return true
        logBeforeInit("ERROR", "Logger not initialized")
        return false
    }

    private fun getLocation(): String {
        val stackTrace: Array<StackTraceElement> = Thread.currentThread().stackTrace
        if (stackTrace.size > 4) {
            val caller: StackTraceElement = stackTrace[4]
            val fileName: String = caller.fileName ?: "Unknown"
            return "$fileName:${caller.lineNumber}"
        }
        return "Unknown:-1"
    }

    private fun formatMessage(level: String, location: String, message: String): String {
        val timestamp: String = LocalDateTime.now().format(timestampFormat)
        val sb: StringBuilder = StringBuilder(timestamp.length + level.length + location.length + message.length + 10)
        sb.append('[').append(timestamp).append("] [").append(level).append("] ")
            .append(location).append(' ').append(message)
        return sb.toString()
    }

    private fun log(level: Level, format: String, vararg args: Any?): Unit {
        if (!enabled[level.ordinal]) return
        val location: String = getLocation()
        val message: String = if (args.isEmpty()) format else String.format(format, *args)
        val formatted: String = formatMessage(level.canonicalName, location, message)
        writeLock.withLock {
            output.append(formatted).append('\n')
            output.flush()
        }
    }

    private fun logPreformatted(level: Level, message: String): Unit {
        if (!enabled[level.ordinal]) return
        val location: String = getLocation()
        val formatted: String = formatMessage(level.canonicalName, location, message)
        writeLock.withLock {
            output.append(formatted).append('\n')
            output.flush()
        }
    }

    @JvmStatic
    fun debug(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.DEBUG, format, *args)
    }

    @JvmStatic
    fun solverDebug(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.DEBUG_SOLVER, format, *args)
    }

    @JvmStatic
    fun info(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.INFO, format, *args)
    }

    @JvmStatic
    fun warn(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.WARN, format, *args)
    }

    @JvmStatic
    fun error(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.ERROR, format, *args)
    }

    @JvmStatic
    fun warnOnce(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        val message: String = if (args.isEmpty()) format else String.format(format, *args)
        val isNew: Boolean = writeLock.withLock {
            if (loggedOnceMessages.contains(message)) false
            else {
                loggedOnceMessages.add(message)
                true
            }
        }
        if (isNew) logPreformatted(Level.WARN, message)
    }

    @JvmStatic
    fun infoOnce(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        val message: String = if (args.isEmpty()) format else String.format(format, *args)
        val isNew: Boolean = writeLock.withLock {
            if (loggedOnceMessages.contains(message)) false
            else {
                loggedOnceMessages.add(message)
                true
            }
        }
        if (isNew) logPreformatted(Level.INFO, message)
    }

    @JvmStatic
    fun errorOnce(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        val message: String = if (args.isEmpty()) format else String.format(format, *args)
        val isNew: Boolean = writeLock.withLock {
            if (loggedOnceMessages.contains(message)) false
            else {
                loggedOnceMessages.add(message)
                true
            }
        }
        if (isNew) logPreformatted(Level.ERROR, message)
    }

    @JvmStatic
    fun result(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.RESULT, format, *args)
    }

    @JvmStatic
    fun benchmark(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.BENCHMARK, format, *args)
    }

    @JvmStatic
    fun mainStep(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.MAINSTEP, format, *args)
    }

    @JvmStatic
    fun subStep(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.SUBSTEP, format, *args)
    }

    @JvmStatic
    fun detail(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.DETAIL, format, *args)
    }

    @JvmStatic
    fun verbose(format: String, vararg args: Any?): Unit {
        if (!requireInit()) return
        log(Level.VERBOSE, format, *args)
    }

    @JvmStatic
    fun isEnabled(level: Level): Boolean {
        if (!initialized) return false
        return enabled[level.ordinal]
    }

    @JvmStatic
    fun close(): Unit {
        writeLock.withLock {
            try {
                if (initialized) {
                    logBeforeInit("INFO", "Logger closed")
                    output.close()
                }
            } catch (e: Exception) {
                logBeforeInit("ERROR", "Failed to close logger: ${e.message}")
            } finally {
                initialized = false
                enabled.fill(false)
                loggedOnceMessages.clear()
            }
        }
    }

}
