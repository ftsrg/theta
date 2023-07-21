package hu.bme.mit.theta.common.pointerstore

import kotlin.math.absoluteValue

class PointerStoreMember(val name: String, val dereferenceLevel: Int = 1)
{
    override fun toString(): String {
        val prefixChar = if (dereferenceLevel < 0) "&" else "*"
        return prefixChar.repeat(dereferenceLevel.absoluteValue) + name
    }

    override fun equals(other: Any?): Boolean {
        if (other !is PointerStoreMember) {
            return false
        }
        return name == other.name && dereferenceLevel == other.dereferenceLevel
    }

    override fun hashCode(): Int {
        var result = name.hashCode()
        result = 31 * result + dereferenceLevel
        return result
    }
}

class PointerStore {
    private val pointerStoreMembers: MutableSet<PointerStoreMember> = mutableSetOf()
    private val pointsTo: MutableSet<Pair<PointerStoreMember, PointerStoreMember>> = mutableSetOf()

    fun addPointer(pointerStoreMember: PointerStoreMember) {
        pointerStoreMembers.add(pointerStoreMember)
        val starPointerStoreMember = PointerStoreMember(pointerStoreMember.name, pointerStoreMember.dereferenceLevel + 1)
        val ampPointerStoreMember = PointerStoreMember(pointerStoreMember.name, pointerStoreMember.dereferenceLevel - 1)
        pointerStoreMembers.add(starPointerStoreMember)
        pointerStoreMembers.add(ampPointerStoreMember)
        addPointsTo(pointerStoreMember, starPointerStoreMember)
        addPointsTo(ampPointerStoreMember, pointerStoreMember)
    }

    fun addPointsTo(pointerStoreMember: PointerStoreMember, pointsTo: PointerStoreMember) {
        if (!pointerStoreMembers.contains(pointerStoreMember)) {
            throw IllegalArgumentException("Pointer $pointerStoreMember is not in the store")
        }
        if (!pointerStoreMembers.contains(pointsTo)) {
            throw IllegalArgumentException("Pointer $pointsTo is not in the store")
        }
        this.pointsTo.add(pointerStoreMember to pointsTo)
    }

    fun pointsTo(pointerStoreMember: PointerStoreMember): Set<PointerStoreMember> {
        if (!pointerStoreMembers.contains(pointerStoreMember)) {
            return emptySet()
        }
        return pointsTo.filter { it.first == pointerStoreMember }.map { it.second }.toSet()
    }
}