package hu.bme.mit.theta.xcfa.cli.witnesses.yaml.witness

import com.google.common.base.Preconditions.checkState
import hu.bme.mit.theta.xcfa.cli.witnesses.yaml.serialization.*

data class Witness2(
    val entries : Set<WitnessEntry>
) {
    companion object {
        fun create(serializedEntries : Set<YamlWitnessEntry>) : Witness2 {
            val entries = mutableSetOf<WitnessEntry>()
            for (entry in serializedEntries) {
                entries.add(WitnessEntry.create(entry))
            }
        }
    }
}

data class WitnessEntry(
    val entry_type: EntryType,
    val metadata: Metadata,
    val content: Content,
) {
    companion object {
        fun create(entry: YamlWitnessEntry): WitnessEntry {
            WitnessEntry(entry.entry_type, Metadata.create(entry.metadata), Content.create(entry.content))
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
                    for (segment in it.segment) {
                        contentItems.add(Segment.create(segment))
                    }
                }
                if (it.cycle != null) {
                    for (cycle in it.cycle) {
                        contentItems.add(Cycle.create(cycle))
                    }
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
    val waypoint: List<Waypoint>? = null,
) : ContentItem, CycleItem {
    companion object {
        fun create(segment: YamlSegment) : Segment {
            if(segment.waypoint!=null) {
                Waypoint.create(segment.waypoint)
            }
        }
    }
}

data class Cycle(
    val items : Set<CycleItem>? = null,
) : ContentItem {
    companion object {
        fun create(cycle: YamlCycle) : Cycle {
            val cycleItems = mutableSetOf<CycleItem>()
            if(cycle.honda!=null) {
                cycleItems.add(Honda.create(cycle.honda))
            }
            if(cycle.segment!=null) {
                for(segment in cycle.segment) {
                    cycleItems.add(Segment.create(segment))
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
)

data class Constraint(
    val value: String,
    val format: FormatEnum? = null,
)

data class Location(
    val file_name: String,
    val line: Int,
    val column: Int? = null,
    val function: String? = null
) {
    init {
        checkState(line >= 1, "line value must be >=1: $line")
        checkState(if(column != null) column>=1 else true, "column value must be >=1: $column")
    }

    companion object {
        fun create(location: YamlLocation) : Location {
            return Location(location.file_name, location.line, location.column, location.function)
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
