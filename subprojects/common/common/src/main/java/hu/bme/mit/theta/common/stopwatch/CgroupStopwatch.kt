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
import hu.bme.mit.theta.common.stopwatch.Stopwatch
import java.io.File
import java.nio.file.Files
import java.util.concurrent.TimeUnit

/**
 * A lightweight, fault-tolerant stopwatch that measures CPU time usage via Linux cgroup accounting.
 *
 * If cgroups are unavailable or permission is denied, it silently falls back to returning 0 for all
 * measurements.
 */
class CgroupStopwatch(prefix: String = "timer") : Stopwatch {
  private val subCgroup: File?
  private var startUsage: Long = 0
  private var endUsage: Long = 0
  private val version: Int

  init {
    version = detectCgroupVersion()
    subCgroup = tryCreateAndEnterSubCgroup(prefix)
  }

  /** Start measuring CPU usage. */
  override fun start() {
    startUsage = readCpuUsageNanos(subCgroup)
  }

  /** Stop measuring CPU usage. */
  override fun stop() {
    endUsage = readCpuUsageNanos(subCgroup)
    cleanup()
  }

  /** Returns the CPU time difference between start() and stop(), in nanoseconds. */
  override fun elapsedNanos(): Long = (endUsage - startUsage).coerceAtLeast(0)

  /** Returns the CPU time difference in milliseconds. */
  override fun elapsedMillis(): Long = TimeUnit.NANOSECONDS.toMillis(elapsedNanos())

  /** Clean up the temporary cgroup and move back to parent if needed. */
  private fun cleanup() {
    try {
      moveSelfToParentCgroup(version)
      if (subCgroup != null) cleanupSubCgroup(subCgroup, version)
    } catch (_: Exception) {
      // silently ignore
    }
  }

  // --- Internal helpers below ---

  companion object {
    fun detectCgroupVersion(): Int {
      if (!System.getProperty("os.name").lowercase().contains("linux")) return 0

      return try {
        val base = File("/sys/fs/cgroup")
        if (!base.exists()) return 0
        if (File(base, "cgroup.controllers").exists()) 2 else 1
      } catch (_: Exception) {
        0
      }
    }
  }

  private fun currentPid(): Long = ProcessHandle.current().pid()

  private fun findAvailableSubCgroup(prefix: String): File? {
    return try {
      val base = File("/sys/fs/cgroup")
      var index = 0
      while (true) {
        val candidate = File(base, "$prefix$index")
        if (!candidate.exists()) return candidate
        index++
      }
      null
    } catch (_: Exception) {
      null
    }
  }

  private fun tryCreateAndEnterSubCgroup(prefix: String): File? {
    return try {
      val sub = findAvailableSubCgroup(prefix) ?: return null
      if (!sub.mkdirs()) return null

      val pid = currentPid()
      if (version == 2) {
        File(sub, "cgroup.procs").appendText("$pid\n")
      } else if (version == 1) {
        val cpuacctDir = File("/sys/fs/cgroup/cpuacct/${sub.name}")
        if (!cpuacctDir.exists()) cpuacctDir.mkdirs()
        File(cpuacctDir, "tasks").appendText("$pid\n")
      }
      sub
    } catch (_: Exception) {
      null
    }
  }

  private fun readCpuUsageNanos(cgroupDir: File?): Long {
    return try {
      if (cgroupDir == null) return 0
      if (version == 2) {
        val statFile = File(cgroupDir, "cpu.stat")
        val usageMicros =
          statFile.useLines { lines ->
            lines
              .firstOrNull { it.startsWith("usage_usec") }
              ?.split(" ")
              ?.getOrNull(1)
              ?.toLongOrNull()
          } ?: return 0
        usageMicros * 1_000
      } else if (version == 1) {
        val usageFile = File("/sys/fs/cgroup/cpuacct/${cgroupDir.name}/cpuacct.usage")
        usageFile.readText().trim().toLongOrNull() ?: 0
      } else 0
    } catch (_: Exception) {
      0
    }
  }

  private fun moveSelfToParentCgroup(version: Int) {
    try {
      val pid = currentPid()
      if (version == 2) {
        File("/sys/fs/cgroup/cgroup.procs").appendText("$pid\n")
      } else if (version == 1) {
        File("/sys/fs/cgroup/cpuacct/tasks").appendText("$pid\n")
      }
    } catch (_: Exception) {
      // ignore
    }
  }

  private fun cleanupSubCgroup(subCgroup: File, version: Int) {
    try {
      if (version == 2) {
        Files.deleteIfExists(subCgroup.toPath())
      } else {
        val cpuacctDir = File("/sys/fs/cgroup/cpuacct/${subCgroup.name}")
        if (cpuacctDir.exists()) Files.delete(cpuacctDir.toPath())
      }
    } catch (_: Exception) {
      // ignore
    }
  }
}
