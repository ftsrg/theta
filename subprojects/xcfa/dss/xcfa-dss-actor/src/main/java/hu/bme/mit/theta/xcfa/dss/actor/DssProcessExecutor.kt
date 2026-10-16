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
package hu.bme.mit.theta.xcfa.dss.actor

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.xcfa.dss.analysis.DssUndecidedQueryException
import hu.bme.mit.theta.xcfa.dss.decomposition.BlockGraph
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

private const val HELLO = "dss-worker-1"
private const val REQUEST_INIT = 1
private const val REQUEST_POST_CONDITION = 2
private const val REQUEST_VIOLATION_CONDITION = 3
private const val REPLY_OK = 0
private const val REPLY_ERROR = 1
private const val INTERRUPT_POLL_MILLIS = 100
private const val WORKER_EXIT_WAIT_SECONDS = 5L

/**
 * Starts the worker process [index] serving [blockIds], which connects back to `localhost:[port]`
 * and calls [serveDssBlocks] there.
 */
fun interface DssWorkerLauncher {
  fun launch(index: Int, blockIds: List<String>, port: Int): Process
}

/** A block analysis that failed in a worker process. */
class DssWorkerException(message: String, remoteStackTrace: String? = null) :
  RuntimeException(if (remoteStackTrace == null) message else "$message\n$remoteStackTrace")

/** Identifies the block graph, so that a worker can check that it decomposed the same way. */
fun BlockGraph.fingerprint(): String =
  blocks.joinToString(";") { b ->
    "${b.id}>${b.successorIds.sorted().joinToString(",")}<${b.predecessorIds.sorted().joinToString(",")}"
  }

/**
 * Runs DSS like [runDssActors], but every block analysis runs in a worker process of its own, so
 * that native solvers that are not thread-safe (legacy Z3, MathSAT on Windows) never run twice in
 * one process. This process keeps the actors, the routing and the quiescence detection; each
 * block's [DssBlockBehavior] is a proxy that sends the message to the worker and returns its
 * answer. Messages travel through [codec], so their expressions must be over the program's
 * variables and [hu.bme.mit.theta.xcfa.dss.analysis.DssAuxVars] only.
 *
 * At most [maxProcesses] workers are started (0: one per block); a worker serving several blocks
 * analyzes them one at a time. A worker that dies fails its blocks with a [DssWorkerException]
 * instead of taking the whole run down with it.
 */
fun runDssActorsInProcesses(
  blockGraph: BlockGraph,
  launcher: DssWorkerLauncher,
  codec: DssExprCodec,
  maxProcesses: Int = 0,
  startupTimeoutMillis: Int = 300_000,
): DssResult {
  val ids = blockGraph.blocks.map { it.id }
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
        check(fingerprint == blockGraph.fingerprint()) {
          "DSS worker $index decomposed the program differently: $fingerprint"
        }
        workers[index] = DssWorkerConnection(groups[index], processes[index], socket, input, codec)
      }
      val workerOf = groups.indices.flatMap { i -> groups[i].map { it to workers[i]!! } }.toMap()
      return runDssActors(blockGraph, behaviorFor = { workerOf.getValue(it.id).behavior(it.id) })
    } finally {
      workers.forEach { it?.close() }
      processes.forEach { it.destroyForcibly() }
    }
  }
}

/** This process's end of the connection to one worker process. */
private class DssWorkerConnection(
  private val blockIds: List<String>,
  private val process: Process,
  private val socket: Socket,
  private val input: DataInputStream,
  private val codec: DssExprCodec,
) {

  private val output = DataOutputStream(BufferedOutputStream(socket.getOutputStream()))

  /** Set once a request was abandoned midway: its answer would be read as the next one's. */
  @Volatile private var broken = false

  fun behavior(blockId: String): DssBlockBehavior =
    object : DssBlockBehavior {
      override fun initialMessages() = request(REQUEST_INIT, blockId) {}

      override fun onPostCondition(message: DssPostConditionMessage) =
        request(REQUEST_POST_CONDITION, blockId) { writeMessage(it, codec, message) }

      override fun onViolationCondition(message: DssViolationConditionMessage) =
        request(REQUEST_VIOLATION_CONDITION, blockId) { writeMessage(it, codec, message) }
    }

  @Synchronized
  private fun request(
    kind: Int,
    blockId: String,
    payload: (DataOutputStream) -> Unit,
  ): List<DssMessage> {
    if (broken) throw DssWorkerException("DSS worker of $blockIds is unusable: $exitDescription")
    try {
      output.writeByte(kind)
      writeString(output, blockId)
      payload(output)
      output.flush()
      return when (awaitReply()) {
        REPLY_OK -> List(input.readInt()) { readMessage(input, codec) }
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

  /**
   * Waits for the first byte of the answer. A blocking socket read ignores interrupts, so it polls:
   * when the run ends, the actor's thread must not wait for a worker still busy with a stale query.
   */
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
    return if (className == DssUndecidedQueryException::class.java.name)
      DssUndecidedQueryException(remote)
    else remote
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

/**
 * The worker side of [runDssActorsInProcesses]: connects to `localhost:[port]` as worker [index]
 * and answers requests with [behaviors], one at a time, until the other side closes the connection.
 * [fingerprint] is this process's [BlockGraph.fingerprint], checked against the main process's.
 */
fun serveDssBlocks(
  port: Int,
  index: Int,
  fingerprint: String,
  behaviors: Map<String, DssBlockBehavior>,
  codec: DssExprCodec,
) {
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
        behavior to if (kind == REQUEST_INIT) null else readMessage(input, codec)
      }
      val answer =
        request.mapCatching { (behavior, message) ->
          when (kind) {
            REQUEST_INIT -> behavior.initialMessages()
            REQUEST_POST_CONDITION -> behavior.onPostCondition(message as DssPostConditionMessage)
            REQUEST_VIOLATION_CONDITION ->
              behavior.onViolationCondition(message as DssViolationConditionMessage)
            else -> error("Unknown DSS worker request $kind")
          }
        }
      answer.fold(
        onSuccess = { messages ->
          output.writeByte(REPLY_OK)
          output.writeInt(messages.size)
          messages.forEach { writeMessage(output, codec, it) }
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

private fun writeMessage(out: DataOutputStream, codec: DssExprCodec, message: DssMessage) {
  when (message) {
    is DssPostConditionMessage -> {
      out.writeByte(MESSAGE_POST_CONDITION)
      writeString(out, message.senderId)
      writeExprs(out, codec, message.postconditions)
      writeExprs(out, codec, message.precision)
      out.writeBoolean(message.nonTrivialForEachPredecessor)
    }
    is DssViolationConditionMessage -> {
      out.writeByte(MESSAGE_VIOLATION_CONDITION)
      writeString(out, message.senderId)
      out.writeBoolean(message.violationCondition != null)
      message.violationCondition?.let { codec.write(out, it) }
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
        input.readBoolean(),
      )
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
