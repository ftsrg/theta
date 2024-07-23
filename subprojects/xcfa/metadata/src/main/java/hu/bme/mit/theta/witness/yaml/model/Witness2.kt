package hu.bme.mit.theta.witness.yaml.model

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.witness.yaml.serialization.*

/**
 * Data classes for the Witness 2.0 format
 * Note: line and column numbers are already changed to 0-indexed!
 * (from the 1-indexed values in the witness)
 */

data class Witness2(
    val entries : Set<WitnessEntry>
) {
    companion object {
        fun create(serializedEntries : Set<YamlWitnessEntry>) : Witness2 {
            val entries = mutableSetOf<WitnessEntry>()
            for (entry in serializedEntries) {
                entries.add(WitnessEntry.create(entry))
            }
            return Witness2(entries)
        }
    }

    // we do not check if that is the only honda or not!
    fun getHonda() : Honda? {
        for (entry in entries) {
            for (item in entry.content.items) {
                if (item is Cycle) {
                    for (item2 in item.items) {
                        if (item2 is Honda) {
                            return item2
                        }
                    }
                }
            }
        }
        return null
    }
}

data class WitnessEntry(
    val entry_type: EntryType,
    val metadata: Metadata,
    val content: Content,
) {
    companion object {
        fun create(entry: YamlWitnessEntry): WitnessEntry {
            return WitnessEntry(entry.entry_type, Metadata.create(entry.metadata), Content.create(entry.content))
        }
    }
}

// -- Metadata --

data class Metadata(
    val format_version: String,
    val uuid: String,
    val creation_time: String,
    val producer: Producer,
    val task: Task,
) {
    companion object {
        fun create(metadata: YamlMetadata) : Metadata {
            return Metadata(metadata.format_version, metadata.uuid, metadata.creation_time, Producer.create(metadata.producer), Task.create(metadata.task))
        }
    }
}

data class Producer(
    val name: String,
    val version: String,
    val configuration: String? = null,
    val command_line: String? = null,
    val description: String? = null,
) {
    companion object {
        fun create(producer: YamlProducer) : Producer {
            return Producer(producer.name, producer.version, producer.configuration, producer.command_line)
        }
    }
}

data class Task(
    val input_files: List<String>,
    val input_file_hashes: Map<String, String>,
    val specification: String,
    val data_model: String,
    val language: String,
) {
    companion object {
        fun create(task: YamlTask) : Task {
            return Task(task.input_files, task.input_file_hashes, task.specification, task.data_model, task.language)
        }
    }
}

// -- Content --

data class Content (
    val items : Set<ContentItem>
) {
    companion object {
        fun create(content: List<YamlContent>) : Content {
            val items = content.map {
                val contentItems = mutableSetOf<ContentItem>()
                if (it.segment != null) {
                    contentItems.add(Segment.create(it.segment))
                }
                if (it.cycle != null) {
                    contentItems.add(Cycle.create(it.cycle))
                }
                contentItems
            }.flatten().toSet()
            return Content(items)
        }
    }
}

interface ContentItem
interface CycleItem

data class Segment(
    val waypoint: Set<Waypoint>,
) : ContentItem, CycleItem {
    companion object {
        fun create(segment: List<YamlSegment>) : Segment {
            val waypoints = mutableSetOf<Waypoint>()
            for(s in segment) {
                if(s.waypoint != null) {
                    waypoints.add(Waypoint.create(s.waypoint))
                }
            }
            return Segment(waypoints)
        }
    }
}

data class Cycle(
    val items : Set<CycleItem>,
) : ContentItem {
    companion object {
        fun create(cycle: List<YamlCycle>) : Cycle {
            val cycleItems = mutableSetOf<CycleItem>()
            for(c in cycle) {
                if(c.honda!=null) {
                    cycleItems.add(Honda.create(c.honda))
                }
                if(c.segment!=null) {
                    cycleItems.add(Segment.create(c.segment))
                }
            }
            return Cycle(cycleItems)
        }
    }
}

data class Waypoint(
    val type: WaypointType,
    val constraint: Constraint? = null,
    val location: Location,
    val action: ActionEnum,
) {
    companion object {
        fun create(waypoint: YamlWaypoint) : Waypoint {
            return Waypoint(waypoint.type,
                waypoint.constraint?.let { Constraint.create(it) }, Location.create(waypoint.location), waypoint.action)
        }
    }
}

data class Constraint(
    val value: String,
    val format: FormatEnum? = null,
) {
    companion object {
        fun create(constraint: YamlConstraint) : Constraint {
            return Constraint(constraint.value, constraint.format)
        }
    }
}

data class Location(
    val file_name: String,
    val line: Int,
    val column: Int? = null,
    val function: String? = null
) {
    init {
        checkState(line >= 0, "line value must be >=0: $line")
        checkState(if(column != null) column>=0 else true, "column value must be >=0: $column")
    }

    companion object {
        fun create(location: YamlLocation) : Location {
            return Location(location.file_name, location.line-1, if(location.column!=null) location.column-1 else null, location.function)
        }
    }
}

data class Honda(
    val location: Location,
    val value: String,
    val format: String,
    val invariant: Boolean,
    val inductive: Boolean
) : CycleItem {
    companion object {
        fun create(honda: YamlHonda) : Honda {
            return Honda(Location.create(honda.location), honda.value, honda.format, honda.invariant, honda.inductive)
        }
    }
}
