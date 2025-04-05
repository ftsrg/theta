/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.tracegeneration

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode
import hu.bme.mit.theta.analysis.expr.StmtAction
import java.io.BufferedReader
import java.io.IOException
import java.io.StringReader

class DoubleEndNodeRemover<S : State, A : Action> {

  private fun isLastInternal(node: ArgNode<S, A>): Boolean {
    return node.state.toString().contains("last_internal")
  }

  private fun isBadLeaf(node: ArgNode<S, A>): Boolean {
    if (isLastInternal(node)) {
      if (node.parent.isEmpty) return false
      val parent = node.parent.get()
      if (parent.parent.isEmpty) return false
      val grandParent = node.parent.get().parent.get()
      return if (node.state == grandParent.state) { // node is covered and parent is checked above
        // bad node
        true
      } else {
        false
      }
    } else {
      var transitionFired = false
      if (node.parent.isPresent && node.parent.get().parent.isPresent) {
        val grandParent = node.parent.get().parent.get()
        if (node.state != grandParent.state) return false

        val state = node.parent.get().state.toString()
        val bufReader = BufferedReader(StringReader(state))
        var line: String? = null
        try {
          while ((bufReader.readLine().also { line = it }) != null) {
            if (line!!.trim { it <= ' ' }.matches("^.*\\(__id_.*__.*\\strue\\).*$".toRegex())) {
              transitionFired = true
            }
          }
        } catch (e: IOException) {
          e.printStackTrace()
        }
        return !transitionFired // if no transition was fired (and state not changed), this is a
        // superfluous node
      } else {
        return false
      }
    }
  }

  companion object {

    /**
     * Mainly of use for XSTS! Collecting nodes that look like there should be traces to it, but
     * shouldn't ("not firing anything" nodes) This should most likely not come up with other
     * formalisms. This removal is executed on them anyways.
     */
    fun <S : State, A : Action> collectBadLeaves(arg: ARG<S, A>): List<ArgNode<S, A>> {
      val instance = DoubleEndNodeRemover<S, A>()
      val badNodes: MutableList<ArgNode<S, A>> = ArrayList()
      arg.nodes
        .filter { obj: ArgNode<S, A> -> obj.isLeaf }
        .forEach { node: ArgNode<S, A> ->
          if (instance.isBadLeaf(node)) {
            badNodes.add(node)
          }
        }
      return badNodes
    }

    fun <S : State?, A : StmtAction?> filterSuperfluousEndNode(trace: Trace<S, A>): Trace<S, A> {
      if (trace.states.size > 3) {
        var transitionFired = false
        val size = trace.states.size
        if (trace.getState(size - 1).toString() == trace.getState(size - 3).toString()) {
          val bufReader = BufferedReader(StringReader(trace.getState(size - 2).toString()))
          var line: String? = null
          try {
            while ((bufReader.readLine().also { line = it }) != null) {
              if (line!!.trim { it <= ' ' }.matches("^\\(__id_.*__.*\\strue\\)*$".toRegex()))
                transitionFired = true
            }
          } catch (e: IOException) {
            e.printStackTrace()
          }
        }
        if (!transitionFired) {
          val newStates = ArrayList(trace.states)
          newStates.removeAt(newStates.size - 1)
          newStates.removeAt(newStates.size - 1)
          val newActions = ArrayList(trace.actions)
          newActions.removeAt(newActions.size - 1)
          newActions.removeAt(newActions.size - 1)
          return Trace.of(newStates, newActions)
        } else {
          return trace
        }
      } else {
        return trace
      }
    }
  }
}
