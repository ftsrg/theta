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
package hu.bme.mit.theta.common.stopwatch

import java.io.File
import java.util.concurrent.TimeUnit

/**
 * A lightweight, fault-tolerant stopwatch that measures CPU time usage via Linux cgroup accounting.
 *
 * Reads CPU time from the cgroup the process is already in (detected via /proc/self/cgroup),
 * so it works under benchexec or any other cgroup manager without needing to create sub-cgroups.
 *
 * If cgroups are unavailable or permission is denied, it silently falls back to returning 0 for all
 * measurements.
 */
class CgroupStopwatch : Stopwatch {
  private val cgroupDir: File?
  private var startUsage: Long = 0
  private var endUsage: Long = 0
  private val version: Int

  init {
    version = detectCgroupVersion()
    cgroupDir = findCurrentCgroupDir()
  }

  override fun start() {
    startUsage = readCpuUsageNanos()
  }

  override fun stop() {
    endUsage = readCpuUsageNanos()
  }

  override fun elapsedNanos(): Long = (endUsage - startUsage).coerceAtLeast(0)

  override fun elapsedMillis(): Long = TimeUnit.NANOSECONDS.toMillis(elapsedNanos())

  private fun readCpuUsageNanos(): Long {
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
        val usageFile = File(cgroupDir, "cpuacct.usage")
        usageFile.readText().trim().toLongOrNull() ?: 0
      } else 0
    } catch (_: Exception) {
      0
    }
  }

  /**
   * Finds the cgroup directory the current process belongs to by reading /proc/self/cgroup.
   *
   * For cgroup v2, /proc/self/cgroup contains a line like "0::/some/path" and the
   * cgroup dir is /sys/fs/cgroup/some/path.
   *
   * For cgroup v1, we look for the cpuacct controller line like "N:cpuacct:/some/path"
   * and the cgroup dir is /sys/fs/cgroup/cpuacct/some/path.
   */
  private fun findCurrentCgroupDir(): File? {
    return try {
      val procCgroup = File("/proc/self/cgroup")
      if (!procCgroup.exists()) return null

      val lines = procCgroup.readLines()

      if (version == 2) {
        // cgroup v2: line format is "0::/path"
        val line = lines.firstOrNull { it.startsWith("0::") } ?: return null
        val path = line.removePrefix("0::")
        val dir = File("/sys/fs/cgroup$path")
        if (dir.exists() && File(dir, "cpu.stat").exists()) dir else null
      } else if (version == 1) {
        // cgroup v1: find cpuacct controller line, format "N:cpuacct,cpu:/path" or "N:cpuacct:/path"
        val line = lines.firstOrNull { entry ->
          val controllers = entry.split(":").getOrNull(1) ?: ""
          controllers.split(",").any { it == "cpuacct" }
        } ?: return null
        val path = line.split(":").getOrNull(2) ?: return null
        val dir = File("/sys/fs/cgroup/cpuacct$path")
        if (dir.exists() && File(dir, "cpuacct.usage").exists()) dir else null
      } else null
    } catch (_: Exception) {
      null
    }
  }

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
}
