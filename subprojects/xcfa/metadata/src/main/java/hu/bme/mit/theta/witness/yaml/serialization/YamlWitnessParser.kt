package hu.bme.mit.theta.witness.yaml.serialization

import com.charleskorn.kaml.Yaml
import hu.bme.mit.theta.witness.yaml.model.Witness2
import kotlinx.serialization.builtins.SetSerializer

class YamlWitnessParser {
    fun parseYaml(yamlContent: String) : Set<YamlWitnessEntry> {
        return Yaml.default.decodeFromString(SetSerializer(YamlWitnessEntry.serializer()), yamlContent)
    }
}

fun main() {
    val yamlContent = """
        - entry_type: "violation_sequence"
          metadata:
            format_version: "2.0"
            uuid: "4412af70-389a-475e-849c-e57e5b92019e"
            creation_time: "2023-09-28T14:42:30+02:00"
            producer:
              name: "CPAchecker"
              version: "2.2.1-svn"
              configuration: "svcomp23"
            task:
              input_files:
              - "while_infinite_loop_1.c"
              input_file_hashes:
                "unsafe-program-example.c": "788d7646eac82f609530b21c31663b77db1405e2b5e4d86a794d2b2e4367fb8a"
              specification: "G ! call(reach_error())"
              data_model: "ILP32"
              language: "C"
          content:
          - segment:
            - waypoint:
                type: "branching"
                action: "follow"
                constraint:
                  value: "true"
                location:
                  file_name: "while_infinite_loop_1.c"
                  line: 22
                  column: 3
          - segment:
            - waypoint:
                type: "branching"
                action: "follow"
                constraint:
                  value: "true"
                location:
                  file_name: "while_infinite_loop_1.c"
                  line: 224
                  column: 34
          - cycle:
            - honda:
                location:
                  file_name: "while_infinite_loop_1.c"
                  line: 24
                  column: 6
                  function: "main"
                value: "1"
                format: "c_expression"
                invariant: true
                inductive: true
            - honda:
                location:
                  file_name: "while_infinite_loop_1.c"
                  line: 24
                  column: 6
                  function: "main"
                value: "2"
                format: "c_expression"
                invariant: true
                inductive: true
            - segment:
                - waypoint:
                    type: "branching"
                    action: "follow"
                    constraint:
                      value: "true"
                    location:
                      file_name: "while_infinite_loop_1.c"
                      line: 22
                      column: 3
    """.trimIndent()

    val serializedEntries = YamlWitnessParser().parseYaml(yamlContent)
    val yamlWitness = Witness2.create(serializedEntries)

}
