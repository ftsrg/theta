/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.metadata

import com.google.common.base.Preconditions.checkState

data class CMetaData(
    val lineNumberStart: Int?,
    val colNumberStart: Int?,
    val lineNumberStop: Int?,
    val colNumberStop: Int?,
    val offsetStart: Int?,
    val offsetEnd: Int?,
    val sourceText: List<String>,
    val scope: List<String>,
) : MetaData() {
    init {
        if(offsetStart != null && offsetEnd != null) {
            checkState(offsetStart<=offsetEnd, "start offset should be before end offset!")
        }
        if(lineNumberStart != null && lineNumberStop != null) {
            checkState(lineNumberStart<=lineNumberStop, "start line should be before stop line!")
        }
    }

    override fun join(m: MetaData): MetaData {
        if (m == EmptyMetaData) return this
        assert(m is CMetaData)

        // the idea here is that we take the earlier start line (and possibly start column with it)
        // and the later stop line (and possibly stop column)
        val jLineNumberStart : Int?
        val jColNumberStart : Int?
        if (m is CMetaData) {
            if(this.lineNumberStart!=null && m.lineNumberStart!=null) {
                if(this.lineNumberStart<m.lineNumberStart) {
                    jLineNumberStart = this.lineNumberStart
                    jColNumberStart = this.colNumberStart
                } else {
                    jLineNumberStart = m.lineNumberStart
                    if(this.lineNumberStart==m.lineNumberStart) {
                        jColNumberStart = listOfNotNull(this.colNumberStart, m.colNumberStart).minOrNull()
                    } else {
                        jColNumberStart = m.colNumberStart
                    }
                }
            } else if(this.lineNumberStart==null && m.lineNumberStart==null) {
                jLineNumberStart = null
                jColNumberStart = null
            } else if(this.lineNumberStart==null) {
                jLineNumberStart = m.lineNumberStart
                jColNumberStart = m.colNumberStart
            } else {
                jLineNumberStart = this.lineNumberStart
                jColNumberStart = this.colNumberStart
            }

            val jLineNumberStop : Int?
            val jColNumberStop : Int?
            if(this.lineNumberStop!=null && m.lineNumberStop!=null) {
                if(this.lineNumberStop>m.lineNumberStop) {
                    jLineNumberStop = this.lineNumberStop
                    jColNumberStop = this.colNumberStop
                } else {
                    jLineNumberStop = m.lineNumberStop
                    if(this.lineNumberStop==m.lineNumberStop) {
                        jColNumberStop = listOfNotNull(this.colNumberStop, m.colNumberStop).minOrNull()
                    } else {
                        jColNumberStop = m.colNumberStop
                    }
                }
            } else if(this.lineNumberStop==null && m.lineNumberStop==null) {
                jLineNumberStop = null
                jColNumberStop = null
            } else if(this.lineNumberStop==null) {
                jLineNumberStop = m.lineNumberStop
                jColNumberStop = m.colNumberStop
            } else {
                jLineNumberStop = this.lineNumberStop
                jColNumberStop = this.colNumberStop
            }

            val jOffsetStart = listOfNotNull(this.offsetStart, m.offsetStart).minOrNull()
            val jOffsetEnd = listOfNotNull(this.offsetEnd, m.offsetEnd).minOrNull()
            val jSourceTexts: List<String> =
            if(this.lineNumberStart!=null && m.lineNumberStart!=null) {
                if (this.lineNumberStart < m.lineNumberStart) {
                    (this.sourceText + m.sourceText)
                } else if(this.lineNumberStart > m.lineNumberStart) {
                    (m.sourceText + this.sourceText)
                } else if(this.colNumberStart!=null && m.colNumberStart!=null) {
                    if(this.colNumberStart < m.colNumberStart) {
                        (this.sourceText + m.sourceText)
                    } else {
                        (m.sourceText + this.sourceText)
                    }
                } else {
                    (this.sourceText + m.sourceText)
                }
            } else {
                (this.sourceText + m.sourceText)
            }

            val scope = if (this.scope.containsAll(m.scope)) this.scope else if (m.scope.containsAll(
                    this.scope
                )
            ) m.scope else emptyList()

            return CMetaData(
                jLineNumberStart, jColNumberStart, jLineNumberStop, jColNumberStop, jOffsetStart, jOffsetEnd,
                jSourceTexts, scope
            )
        } else {
            throw RuntimeException("CMetaData can only be joined with CMetaData")
        }
    }

    override fun toString(): String {
        val source = sourceText.toString()
        return "%d:%d-%d:%d [%s]".format(lineNumberStart ?: -1, colNumberStart ?: -1, lineNumberStop ?: -1, colNumberStop ?: -1, if(source.length > 25) source.substring(0, 20) + "... " + source.substring(source.length - 10, source.length) else sourceText)
    }

}
