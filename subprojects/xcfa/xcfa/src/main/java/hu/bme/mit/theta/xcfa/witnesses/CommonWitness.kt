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
package hu.bme.mit.theta.xcfa.witnesses

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.xcfa.model.XcfaEdge
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Paths
import java.security.DigestInputStream
import java.security.MessageDigest
import java.security.NoSuchAlgorithmException
import java.text.DateFormat
import java.text.SimpleDateFormat
import java.util.*

data class WitnessNode(
  val id: String,
  val entry: Boolean = false,
  val sink: Boolean = false,
  val violation: Boolean = false,
  val xcfaLocations: Map<Int, List<XcfaLocation>> = emptyMap(),
  val cSources: Map<Int, List<String>> = emptyMap(),
  val globalState: ExplState? = null,
) : State {

  override fun isBottom(): Boolean {
    error("Not applicable for witness states.")
  }
}

data class WitnessEdge(
  val sourceId: String,
  val targetId: String,
  val assumption: String? = null,
  val assumption_scope: String? = null,
  val assumption_resultfunction: String? = null,
  val control: Boolean? = null,
  val startline: Int? = null,
  val endline: Int? = null,
  val startoffset: Int? = null,
  val endoffset: Int? = null,
  val startcol: Int? = null,
  val endcol: Int? = null,
  val enterLoopHead: Boolean = false,
  val enterFunction: String? = null,
  val returnFromFunction: String? = null,
  val threadId: String? = null,
  val createThread: String? = null,
  val stmt: String? = null,
  val cSource: String? = null,
  val edge: XcfaEdge? = null,
) : Action {}

fun createTaskHash(programFile: String): String {
  var md: MessageDigest? = null
  try {
    md = MessageDigest.getInstance("SHA-256")
  } catch (e: NoSuchAlgorithmException) {
    e.printStackTrace()
  }
  try {
    Files.newInputStream(Paths.get(programFile)).use { `is` ->
      DigestInputStream(`is`, md).use { dis -> while (dis.read() != -1) {} }
    }
  } catch (e: IOException) {
    e.printStackTrace()
  }
  checkNotNull(md)
  val digest = md.digest()
  return bytesToHex(digest)
}

// source: https://www.baeldung.com/sha-256-hashing-java
fun bytesToHex(hash: ByteArray): String {
  val hexString = StringBuilder(2 * hash.size)
  for (i in hash.indices) {
    val hex = Integer.toHexString(0xff and hash[i].toInt())
    if (hex.length == 1) {
      hexString.append('0')
    }
    hexString.append(hex)
  }
  return hexString.toString()
}

fun getIsoDate(): String {
  val tz: TimeZone = TimeZone.getTimeZone("UTC")
  val df: DateFormat =
    SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss'Z'") // Quoted "Z" to indicate UTC, no timezone offset

  df.timeZone = tz
  return df.format(Date())
}
