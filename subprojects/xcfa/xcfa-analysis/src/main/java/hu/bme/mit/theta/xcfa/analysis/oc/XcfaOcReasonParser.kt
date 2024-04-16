package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*

internal class XcfaOcReasonParser(
    private val rels: Set<R>,
    private val events: Set<E>,
) {

    fun parse(input: String): Reason {
        val i = input.trim()

        if (i == "[]") {
            return CombinedReason(emptyList())
        }

        if (i.startsWith("[") && i.endsWith("]")) {
            val parts = mutableListOf<String>()
            var str = i.substring(1, i.length - 1)
            var squareBracketCount = 0
            var j = 0
            while (j < str.length) {
                if (str[j] == '[') squareBracketCount++
                if (str[j] == ']') squareBracketCount--
                if (str[j] == ';' && squareBracketCount == 0) {
                    parts.add(str.substring(0, j))
                    str = str.substring(j + 1)
                    j = 0
                } else {
                    j++
                }
            }
            parts.add(str)
            return CombinedReason(parts.map { parse(it) })
        }

        if (i.startsWith("REL(") && i.endsWith(")")) {
            val relStr = i.substring(4, i.length - 1).trim()
            val rel = rels.find { it.decl.name == relStr } ?: error("Unknown relation: $relStr")
            return RelationReason(rel)
        }

        if (i.startsWith("WS(") && i.endsWith(")")) {
            val parts = i.substring(3, i.length - 1).split(",").map { it.trim() }
            val rfStr = parts[0]
            val wStr = parts[1]
            val wBeforeRfStr = parts.subList(2, parts.size).joinToString(",")

            val rf = rels.find { it.decl.name == rfStr } ?: error("Unknown relation: $rfStr")
            val w = events.find { it.const.name == wStr } ?: error("Unknown event: $wStr")
            val wBeforeRf = parse(wBeforeRfStr)
            return WriteSerializationReason(rf, w, wBeforeRf)
        }

        if (i.startsWith("FR(") && i.endsWith(")")) {
            val parts = i.substring(3, i.length - 1).split(",").map { it.trim() }
            val rfStr = parts[0]
            val wStr = parts[1]
            val wAfterRfStr = parts.subList(2, parts.size).joinToString(",")

            val rf = rels.find { it.decl.name == rfStr } ?: error("Unknown relation: $rfStr")
            val w = events.find { it.const.name == wStr } ?: error("Unknown event: $wStr")
            val wAfterRf = parse(wAfterRfStr)
            return FromReadReason(rf, w, wAfterRf)
        }

        if (i == "PO()") return PoReason
        error("Unknown reason format: $input")
    }
}
