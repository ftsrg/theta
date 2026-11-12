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
package hu.bme.mit.theta.xcfa.analysis.dss.actor

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssBlockCutRequest
import hu.bme.mit.theta.xcfa.analysis.dss.analysis.DssUndecidedQueryException
import hu.bme.mit.theta.xcfa.analysis.dss.decomposition.BlockGraph
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.EOFException
import java.io.IOException
import java.net.InetAddress
import java.net.ServerSocket
import java.net.Socket
import java.net.SocketTimeoutException
import java.util.concurrent.TimeUnit
import kotlin.concurrent.thread

private const val HELLO = "dss-worker-1"
private const val REQUEST_INIT = 1
private const val REQUEST_POST_CONDITION = 2
private const val REQUEST_VIOLATION_CONDITION = 3
private const val REQUEST_WITNESS = 4
private const val REQUEST_RESTRICTION = 5
private const val REPLY_OK = 0
private const val REPLY_ERROR = 1
private const val INTERRUPT_POLL_MILLIS = 100
private const val WORKER_EXIT_WAIT_SECONDS = 5L
private const val PARENT_POLL_MILLIS = 500L
private const val WORKER_ORPHANED_EXIT_CODE = 3

/** Starts worker [index] for [blockIds]; it connects back to [port] and runs [serveDssBlocks]. */
fun interface DssWorkerLauncher {
  fun launch(index: Int, blockIds: List<String>, port: Int): Process
}

class DssWorkerException(message: String, remoteStackTrace: String? = null) :
  RuntimeException(if (remoteStackTrace == null) message else "$message\n$remoteStackTrace")

fun BlockGraph.fingerprint(): String =
  blocks.joinToString(";") { b ->
    "${b.id}>${b.successorIds.sorted().joinToString(",")}<${b.predecessorIds.sorted().joinToString(",")}"
  }

/** The workers of a multi-network run must decompose every network the same way. */
fun fingerprint(blockGraphs: List<BlockGraph>): String =
  blockGraphs.joinToString("|") { it.fingerprint() }

/** [runDssActors] with every block analysis in a worker process, so any solver runs in parallel. */
fun runDssActorsInProcesses(
  blockGraph: BlockGraph,
  launcher: DssWorkerLauncher,
  codec: DssExprCodec,
  maxProcesses: Int = 0,
  startupTimeoutMillis: Int = 300_000,
  witnesses: MutableMap<String, DssBlockWitness>? = null,
): DssResult =
  runDssNetworksInProcesses(
      listOf(blockGraph),
      launcher,
      { codec },
      maxProcesses = maxProcesses,
      startupTimeoutMillis = startupTimeoutMillis,
      witnesses = witnesses,
    )
    .result

/**
 * [runDssNetworks] with every block analysis in a worker process; [codecOf] gives the codec of a
 * block's own program. The coordinator runs in this process.
 */
fun runDssNetworksInProcesses(
  blockGraphs: List<BlockGraph>,
  launcher: DssWorkerLauncher,
  codecOf: (String) -> DssExprCodec,
  coordinator: DssCoordinatorFactory? = null,
  maxProcesses: Int = 0,
  startupTimeoutMillis: Int = 300_000,
  witnesses: MutableMap<String, DssBlockWitness>? = null,
): DssRun {
  val ids = blockGraphs.flatMap { graph -> graph.blocks.map { it.id } }
  val processCount = if (maxProcesses <= 0) ids.size else minOf(maxProcesses, ids.size)
  val groups = List(processCount) { i -> ids.filterIndexed { j, _ -> j % processCount == i } }
  val workers = arrayOfNulls<DssWorkerConnection>(processCount)
  val processes = mutableListOf<Process>()
  ServerSocket(0, processCount, InetAddress.getLoopbackAddress()).use { server ->
    try {
      groups.forEachIndexed { i, group -> processes += launcher.launch(i, group, server.localPort) }
      val deadline = System.currentTimeMillis() + startupTimeoutMillis
      server.soTimeout = INTERRUPT_POLL_MILLIS
      repeat(processCount) {
        var socket: Socket? = null
        while (socket == null) {
          try {
            socket = server.accept()
          } catch (_: SocketTimeoutException) {
            val dead =
              processes.withIndex().firstOrNull { (i, p) -> workers[i] == null && !p.isAlive }
            if (dead != null) {
              throw DssWorkerException(
                "DSS worker ${dead.index} (${groups[dead.index]}) exited with code " +
                  "${dead.value.exitValue()} before connecting"
              )
            }
            if (System.currentTimeMillis() > deadline) {
              throw DssWorkerException(
                "DSS worker processes did not connect within $startupTimeoutMillis ms"
              )
            }
            if (Thread.interrupted()) throw InterruptedException()
          }
        }
        socket.soTimeout = 0
        socket.tcpNoDelay = true
        val input = DataInputStream(BufferedInputStream(socket.getInputStream()))
        check(readString(input) == HELLO) { "Unexpected DSS worker handshake" }
        val index = input.readInt()
        val fingerprint = readString(input)
        check(fingerprint == fingerprint(blockGraphs)) {
          "DSS worker $index decomposed the program differently: $fingerprint"
        }
        workers[index] =
          DssWorkerConnection(groups[index], processes[index], socket, input, codecOf)
      }
      val workerOf = groups.indices.flatMap { i -> groups[i].map { it to workers[i]!! } }.toMap()
      val result =
        runDssNetworks(
          blockGraphs.map { graph ->
            DssNetwork(graph) { workerOf.getValue(it.id).behavior(it.id) }
          },
          coordinator,
        )
      // Before the workers are closed: a worker left unusable by the run only loses its blocks
      witnesses?.let { collected ->
        for ((id, worker) in workerOf) {
          runCatching { worker.behavior(id).witness() }.getOrNull()?.let { collected[id] = it }
        }
      }
      return result
    } finally {
      workers.forEach { it?.close() }
      processes.forEach { it.destroyForcibly() }
    }
  }
}

private class DssWorkerConnection(
  private val blockIds: List<String>,
  private val process: Process,
  private val socket: Socket,
  private val input: DataInputStream,
  private val codecOf: (String) -> DssExprCodec,
) {

  private val output = DataOutputStream(BufferedOutputStream(socket.getOutputStream()))

  @Volatile private var broken = false

  fun behavior(blockId: String): DssBlockBehavior {
    val codec = codecOf(blockId)
    return object : DssBlockBehavior {
      override fun initialMessages() = request(REQUEST_INIT, blockId, codec) {}

      override fun onPostCondition(message: DssPostConditionMessage) =
        request(REQUEST_POST_CONDITION, blockId, codec) { writeMessage(it, codec, message) }

      override fun onViolationCondition(message: DssViolationConditionMessage) =
        request(REQUEST_VIOLATION_CONDITION, blockId, codec) { writeMessage(it, codec, message) }

      override fun onRestriction(message: DssRestrictionMessage) =
        request(REQUEST_RESTRICTION, blockId, codec) { writeMessage(it, codec, message) }

      override fun witness() = request(REQUEST_WITNESS, blockId, {}) { readWitness(it, codec) }
    }
  }

  private fun request(
    kind: Int,
    blockId: String,
    codec: DssExprCodec,
    payload: (DataOutputStream) -> Unit,
  ): List<DssMessage> =
    request(kind, blockId, payload) { input -> List(input.readInt()) { readMessage(input, codec) } }

  @Synchronized
  private fun <T> request(
    kind: Int,
    blockId: String,
    payload: (DataOutputStream) -> Unit,
    reply: (DataInputStream) -> T,
  ): T {
    if (broken) throw DssWorkerException("DSS worker of $blockIds is unusable: $exitDescription")
    try {
      output.writeByte(kind)
      writeString(output, blockId)
      payload(output)
      output.flush()
      return when (awaitReply()) {
        REPLY_OK -> reply(input)
        REPLY_ERROR -> throw remoteException(blockId)
        else -> error("Unexpected DSS worker reply")
      }
    } catch (e: IOException) {
      broken = true
      throw DssWorkerException("DSS worker of $blockIds failed on $blockId: $exitDescription ($e)")
    } catch (e: InterruptedException) {
      broken = true
      throw e
    }
  }

  /** Polls, since a blocking socket read ignores interrupts. */
  private fun awaitReply(): Int {
    socket.soTimeout = INTERRUPT_POLL_MILLIS
    try {
      while (true) {
        try {
          return input.read().also { if (it < 0) throw EOFException() }
        } catch (_: SocketTimeoutException) {
          if (Thread.interrupted()) throw InterruptedException()
        }
      }
    } finally {
      socket.soTimeout = 0
    }
  }

  private fun remoteException(blockId: String): RuntimeException {
    val className = readString(input)
    val message = readString(input)
    val stackTrace = readString(input)
    val remote = DssWorkerException("$className in the worker of $blockId: $message", stackTrace)
    return when (className) {
      DssUndecidedQueryException::class.java.name -> DssUndecidedQueryException(remote)
      DssBlockCutRequest::class.java.name -> DssBlockCutRequest(blockId, remote)
      else -> remote
    }
  }

  private val exitDescription: String
    get() =
      if (process.waitFor(WORKER_EXIT_WAIT_SECONDS, TimeUnit.SECONDS))
        "the process exited with code ${process.exitValue()}"
      else "the process is still running"

  fun close() {
    try {
      socket.close()
    } catch (_: IOException) {}
  }
}

/** Worker side of [runDssActorsInProcesses]. */
fun serveDssBlocks(
  port: Int,
  index: Int,
  fingerprint: String,
  behaviors: Map<String, DssBlockBehavior>,
  codec: DssExprCodec,
) = serveDssBlocks(port, index, fingerprint, behaviors) { codec }

/** Worker side of [runDssNetworksInProcesses]; [codecOf] gives the codec of a block's program. */
fun serveDssBlocks(
  port: Int,
  index: Int,
  fingerprint: String,
  behaviors: Map<String, DssBlockBehavior>,
  codecOf: (String) -> DssExprCodec,
) {
  // A worker busy in a solver call would notice a killed main process only afterwards
  ProcessHandle.current().parent().ifPresent { parent ->
    thread(isDaemon = true, name = "dss-worker-$index-parent-watch") {
      while (parent.isAlive) Thread.sleep(PARENT_POLL_MILLIS)
      Runtime.getRuntime().halt(WORKER_ORPHANED_EXIT_CODE)
    }
  }
  Socket(InetAddress.getLoopbackAddress(), port).use { socket ->
    socket.tcpNoDelay = true
    val input = DataInputStream(BufferedInputStream(socket.getInputStream()))
    val output = DataOutputStream(BufferedOutputStream(socket.getOutputStream()))
    writeString(output, HELLO)
    output.writeInt(index)
    writeString(output, fingerprint)
    output.flush()
    while (true) {
      val kind =
        try {
          input.readUnsignedByte()
        } catch (_: EOFException) {
          return
        } catch (_: IOException) {
          return
        }
      val blockId = readString(input)
      // A request that cannot be read leaves the stream out of step: answer it, then hang up
      val request = runCatching {
        val behavior = behaviors[blockId] ?: error("DSS worker $index does not serve $blockId")
        behavior to
          if (kind == REQUEST_INIT || kind == REQUEST_WITNESS) null
          else readMessage(input, codecOf(blockId))
      }
      val codec by lazy { codecOf(blockId) }
      val answer: Result<(DataOutputStream) -> Unit> =
        request.mapCatching { (behavior, message) ->
          if (kind == REQUEST_WITNESS) {
            val witness = behavior.witness()
            return@mapCatching { out -> writeWitness(out, codec, witness) }
          }
          val messages =
            when (kind) {
              REQUEST_INIT -> behavior.initialMessages()
              REQUEST_POST_CONDITION -> behavior.onPostCondition(message as DssPostConditionMessage)
              REQUEST_VIOLATION_CONDITION ->
                behavior.onViolationCondition(message as DssViolationConditionMessage)
              REQUEST_RESTRICTION -> behavior.onRestriction(message as DssRestrictionMessage)
              else -> error("Unknown DSS worker request $kind")
            }
          return@mapCatching { out ->
            out.writeInt(messages.size)
            messages.forEach { writeMessage(out, codec, it) }
          }
        }
      answer.fold(
        onSuccess = { write ->
          output.writeByte(REPLY_OK)
          write(output)
        },
        onFailure = { e ->
          output.writeByte(REPLY_ERROR)
          writeString(output, e.javaClass.name)
          writeString(output, e.message ?: e.toString())
          writeString(output, e.stackTraceToString())
        },
      )
      output.flush()
      if (request.isFailure) return
    }
  }
}

private const val MESSAGE_POST_CONDITION = 1
private const val MESSAGE_VIOLATION_CONDITION = 2
private const val MESSAGE_RESTRICTION = 3

/** A restriction's targets are routing only: the worker's block is the target. */
private fun writeMessage(out: DataOutputStream, codec: DssExprCodec, message: DssMessage) {
  when (message) {
    is DssPostConditionMessage -> {
      out.writeByte(MESSAGE_POST_CONDITION)
      writeString(out, message.senderId)
      writeExprs(out, codec, message.postconditions)
      writeExprs(out, codec, message.precision)
      out.writeInt(message.version)
      out.writeInt(message.inputs.size)
      for ((sender, version) in message.inputs) {
        writeString(out, sender)
        out.writeInt(version)
      }
      out.writeBoolean(message.restricted)
      out.writeBoolean(message.observerOnly)
    }
    is DssViolationConditionMessage -> {
      out.writeByte(MESSAGE_VIOLATION_CONDITION)
      writeString(out, message.senderId)
      out.writeBoolean(message.violationCondition != null)
      message.violationCondition?.let { codec.write(out, it) }
    }
    is DssRestrictionMessage -> {
      out.writeByte(MESSAGE_RESTRICTION)
      writeString(out, message.senderId)
      codec.write(out, message.restriction)
    }
    else -> error("A block behavior does not send ${message.type} messages")
  }
}

private fun readMessage(input: DataInputStream, codec: DssExprCodec): DssMessage =
  when (val kind = input.readUnsignedByte()) {
    MESSAGE_POST_CONDITION ->
      DssPostConditionMessage(
        readString(input),
        readExprs(input, codec),
        readExprs(input, codec).toSet(),
        version = input.readInt(),
        inputs = List(input.readInt()) { readString(input) to input.readInt() }.toMap(),
        restricted = input.readBoolean(),
        observerOnly = input.readBoolean(),
      )
    MESSAGE_RESTRICTION -> DssRestrictionMessage(readString(input), codec.read(input))
    MESSAGE_VIOLATION_CONDITION ->
      DssViolationConditionMessage(
        readString(input),
        if (input.readBoolean()) codec.read(input) else null,
      )
    else -> error("Unknown DSS message kind $kind")
  }

private fun writeExprs(
  out: DataOutputStream,
  codec: DssExprCodec,
  exprs: Collection<Expr<BoolType>>,
) {
  out.writeInt(exprs.size)
  exprs.forEach { codec.write(out, it) }
}

private fun readExprs(input: DataInputStream, codec: DssExprCodec): List<Expr<BoolType>> =
  List(input.readInt()) { codec.read(input) }

private const val RECORD_ALL_PATHS = 1
private const val RECORD_PATH = 2

private fun writeWitness(out: DataOutputStream, codec: DssExprCodec, witness: DssBlockWitness?) {
  out.writeBoolean(witness != null)
  if (witness == null) return
  writeInvariants(out, codec, witness.invariants)
  writeInvariants(out, codec, witness.errorFreeInvariants)
  out.writeInt(witness.violations.size)
  for (record in witness.violations) {
    when (record) {
      is DssAllPathsViolation -> {
        out.writeByte(RECORD_ALL_PATHS)
        out.writeInt(record.targets.size)
        for ((location, condition) in record.targets) {
          codec.writeLocation(out, location)
          codec.write(out, condition)
        }
      }
      is DssPathViolation -> {
        out.writeByte(RECORD_PATH)
        out.writeInt(record.edges.size)
        record.edges.forEach { codec.writeEdge(out, it) }
        out.writeBoolean(record.reachedReceived)
      }
    }
    codec.write(out, record.condition)
    out.writeInt(record.received.size)
    for ((sender, condition) in record.received) {
      writeString(out, sender)
      codec.write(out, condition)
    }
  }
  writeExprs(out, codec, witness.reported)
}

private fun readWitness(input: DataInputStream, codec: DssExprCodec): DssBlockWitness? {
  if (!input.readBoolean()) return null
  val invariants = readInvariants(input, codec)
  val errorFreeInvariants = readInvariants(input, codec)
  val violations =
    List(input.readInt()) {
      val kind = input.readUnsignedByte()
      val targets =
        if (kind == RECORD_ALL_PATHS)
          List(input.readInt()) { codec.readLocation(input) to codec.read(input) }.toMap()
        else null
      val edges = if (kind == RECORD_PATH) List(input.readInt()) { codec.readEdge(input) } else null
      val reachedReceived = kind == RECORD_PATH && input.readBoolean()
      val condition = codec.read(input)
      val received = List(input.readInt()) { readString(input) to codec.read(input) }
      when (kind) {
        RECORD_ALL_PATHS -> DssAllPathsViolation(condition, targets!!, received)
        RECORD_PATH -> DssPathViolation(condition, edges!!, reachedReceived, received)
        else -> error("Unknown DSS violation record kind $kind")
      }
    }
  return DssBlockWitness(invariants, violations, readExprs(input, codec), errorFreeInvariants)
}

private fun writeInvariants(
  out: DataOutputStream,
  codec: DssExprCodec,
  invariants: Map<XcfaLocation, List<Expr<BoolType>>>?,
) {
  out.writeBoolean(invariants != null)
  if (invariants == null) return
  out.writeInt(invariants.size)
  for ((location, states) in invariants) {
    codec.writeLocation(out, location)
    writeExprs(out, codec, states)
  }
}

private fun readInvariants(
  input: DataInputStream,
  codec: DssExprCodec,
): Map<XcfaLocation, List<Expr<BoolType>>>? =
  if (input.readBoolean())
    List(input.readInt()) { codec.readLocation(input) to readExprs(input, codec) }.toMap()
  else null
