/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.gson

import com.google.gson.Gson
import com.google.gson.TypeAdapter
import com.google.gson.reflect.TypeToken
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonToken
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.xcfa.model.*
import java.util.*

class XcfaAdapter(val gsonSupplier: () -> Gson) : TypeAdapter<XCFA>() {

    private lateinit var gson: Gson
    override fun write(writer: JsonWriter, value: XCFA) {
        initGson()
        writer.beginObject()
        writer.name("name").value(value.name)
        //vars
        writer.name("vars")
        gson.toJson(gson.toJsonTree(value.vars), writer)

        //procedures
        writer.name("procedures").beginArray()
        for (xcfaProcedure in value.procedures) {
            writer.beginObject()
            writer.name("name").value(xcfaProcedure.name)
            writer.name("params")
            gson.toJson(gson.toJsonTree(xcfaProcedure.params), writer)
            writer.name("vars")
            gson.toJson(gson.toJsonTree(xcfaProcedure.vars), writer)
            writer.name("locs")
            gson.toJson(gson.toJsonTree(xcfaProcedure.locs), writer)
            writer.name("edges")
            writer.beginArray().also {
                xcfaProcedure.edges.forEach {
                    writer.beginObject()
                        .name("source").value(it.source.name)
                        .name("target").value(it.target.name)
                        .name("label")
                    gson.toJson(gson.toJsonTree(it.label), writer)
                    writer.endObject()
                }
            }.endArray()

            writer.endObject()
        }
        writer.endArray()

        //initProcedures
        writer.name("initProcedures").beginArray()
        value.initProcedures.forEach {
            writer.beginObject()
            writer.name("params")
            gson.toJson(gson.toJsonTree(it.second), writer)
            writer.name("procedure").value(it.first.name)
            writer.endObject()
        }
        writer.endArray()

        writer.endObject()
    }

    override fun read(reader: JsonReader): XCFA {
        initGson()

        reader.beginObject()
        lateinit var name: String
        lateinit var vars: Set<XcfaGlobalVar>
        lateinit var xcfaProcedures: Map<String, XcfaProcedure>
        lateinit var initProcedures: List<Pair<XcfaProcedure, List<Expr<*>>>>

        val varsType = object : TypeToken<Set<XcfaGlobalVar>>() {}.type

        lateinit var xcfa: XCFA
        while (reader.peek() != JsonToken.END_OBJECT) {
            val nextName = reader.nextName()
            when (nextName) {
                "name" -> name = reader.nextString()
                "vars" -> vars = gson.fromJson(reader, varsType)
                "procedures" -> {
                    xcfa = XCFA(name, vars)
                    xcfaProcedures = parseProcedures(reader, xcfa)
                }

                "initProcedures" -> initProcedures = parseInitProcedures(reader, xcfaProcedures)
            }
        }
        reader.endObject()

        return xcfa.recreate(xcfaProcedures.values.toSet(), initProcedures)
    }

    private fun parseInitProcedures(
        reader: JsonReader,
        procedures: Map<String, XcfaProcedure>): List<Pair<XcfaProcedure, List<Expr<*>>>> {
        reader.beginArray()
        val ret = ArrayList<Pair<XcfaProcedure, List<Expr<*>>>>()
        val paramsType = object : TypeToken<List<Expr<*>>>() {}.type
        while (reader.peek() != JsonToken.END_ARRAY) {
            reader.beginObject()
            lateinit var params: List<Expr<*>>
            lateinit var procedure: XcfaProcedure
            while (reader.peek() != JsonToken.END_OBJECT) {
                when (reader.nextName()) {
                    "params" -> params = gson.fromJson(reader, paramsType)
                    "procedure" -> procedure = checkNotNull(procedures[reader.nextString()])
                }
            }
            ret.add(Pair(procedure, params))
            reader.endObject()
        }
        reader.endArray()
        return ret
    }

    private fun parseProcedures(reader: JsonReader, xcfa: XCFA): Map<String, XcfaProcedure> {
        reader.beginArray()
        val ret = LinkedHashMap<String, XcfaProcedure>()
        val paramsType = object : TypeToken<List<Pair<VarDecl<*>, ParamDirection>>>() {}.type
        val varsType = object : TypeToken<Set<VarDecl<*>>>() {}.type
        val locsType = object : TypeToken<Set<XcfaLocation>>() {}.type
        val labelType = object : TypeToken<XcfaLabel>() {}.type

        while (reader.peek() != JsonToken.END_ARRAY) {
            reader.beginObject()
            lateinit var name: String
            lateinit var params: List<Pair<VarDecl<*>, ParamDirection>>
            lateinit var vars: Set<VarDecl<*>>
            lateinit var locs: Map<String, XcfaLocation>
            val edges: MutableSet<XcfaEdge> = LinkedHashSet()
            lateinit var initLoc: XcfaLocation
            var finalLoc: XcfaLocation? = null
            var errorLoc: XcfaLocation? = null

            while (reader.peek() != JsonToken.END_OBJECT) {
                when (reader.nextName()) {
                    "name" -> name = reader.nextString()
                    "params" -> params = gson.fromJson(reader, paramsType)
                    "vars" -> vars = gson.fromJson(reader, varsType)
                    "locs" -> {
                        val locations: Set<XcfaLocation> = gson.fromJson(reader, locsType)
                        locations.forEach {
                            if (it.error) errorLoc = it
                            if (it.initial) initLoc = it
                            if (it.final) finalLoc = it
                        }
                        locs = locations.associateBy { it.name }
                    }

                    "edges" -> {
                        reader.beginArray()
                        while (reader.peek() != JsonToken.END_ARRAY) {
                            reader.beginObject()
                            lateinit var source: XcfaLocation
                            lateinit var target: XcfaLocation
                            lateinit var label: XcfaLabel
                            while (reader.peek() != JsonToken.END_OBJECT) {
                                when (reader.nextName()) {
                                    "source" -> source = checkNotNull(locs[reader.nextString()])
                                    "target" -> target = checkNotNull(locs[reader.nextString()])
                                    "label" -> label = gson.fromJson(reader, labelType)
                                }
                            }
                            val edge = XcfaEdge(source, target, label)
                            edges.add(edge)
                            source.outgoingEdges.add(edge)
                            target.incomingEdges.add(edge)
                            reader.endObject()
                        }
                        reader.endArray()
                    }
                }
            }
            ret[name] = XcfaProcedure(name, params, vars, locs.values.toSet(), edges, initLoc,
                Optional.ofNullable(finalLoc),
                Optional.ofNullable(errorLoc)).also { it.parent = xcfa }
            reader.endObject()
        }
        reader.endArray()
        return ret
    }

    private fun initGson() {
        if (!this::gson.isInitialized) gson = gsonSupplier()
    }

}