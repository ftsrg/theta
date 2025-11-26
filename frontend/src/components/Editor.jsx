import React, { useEffect, useRef } from 'react'
import * as monaco from 'monaco-editor'
import { Box } from '@mui/material'
import EditorToolbar from './EditorToolbar'
import { registerSmtLib } from '../monaco-languages/smtlib'
import { registerXsts } from '../monaco-languages/xsts'

// Register custom languages once
let languagesRegistered = false
if (!languagesRegistered) {
  registerSmtLib(monaco)
  registerXsts(monaco)
  languagesRegistered = true
}

export default function Editor({ code, onChange, onPositionChange, examples, properties, selectedProperty, mode, modesConfig, safetyResult, verifyRunning, verificationValid, witnessData, onSelectExample, onSelectProperty }) {
  const ref = useRef(null)
  const editorRef = useRef(null)
  const decorationsRef = useRef([])
  const language = modesConfig[mode]?.language || 'plaintext'

  useEffect(() => {
    editorRef.current = monaco.editor.create(ref.current, {
      value: code || '',
      language: language,
      automaticLayout: true,
      theme: 'vs-dark',
      minimap: { enabled: false },
      renderWhitespace: 'none',
      fontSize: 13,
      lineHeight: 20,
      smoothScrolling: true,
      scrollbar: { verticalScrollbarSize: 8, horizontalScrollbarSize: 8 }
    })
    const model = editorRef.current.getModel()
    const sub = model.onDidChangeContent(() => onChange(model.getValue()))
    const posSub = editorRef.current.onDidChangeCursorPosition((e) => {
      const p = e.position
      if (onPositionChange) onPositionChange({ line: p.lineNumber, column: p.column })
    })
    return () => {
      sub.dispose()
      posSub.dispose()
      editorRef.current.dispose()
    }
  }, [])

  useEffect(() => {
    const model = editorRef.current && editorRef.current.getModel()
    if (model && model.getValue() !== code) model.setValue(code)
  }, [code])

  useEffect(() => {
    const model = editorRef.current && editorRef.current.getModel()
    if (model) {
      monaco.editor.setModelLanguage(model, language)
    }
  }, [language])

  // Place markers for witness waypoints
  useEffect(() => {
    if (!editorRef.current || !witnessData) {
      // Clear existing decorations when no witness data
      if (decorationsRef.current.length > 0) {
        decorationsRef.current = editorRef.current?.deltaDecorations(decorationsRef.current, []) || []
      }
      return
    }

    // Extract waypoints from witness data
    const waypoints = []
    if (Array.isArray(witnessData)) {
      for (const entry of witnessData) {
        if (entry?.content?.length) {
          for (const segment of entry.content) {
            if (segment?.segment && Array.isArray(segment.segment)) {
              for (const item of segment.segment) {
                if (item?.waypoint) {
                  // waypoint is an object, not an array
                  waypoints.push(item.waypoint)
                }
              }
            }
          }
        }
      }
    }

    // Create decorations for each waypoint with location (include index)
    const newDecorations = []
    for (let idx = 0; idx < waypoints.length; idx++) {
      const wp = waypoints[idx]
      if (wp?.location?.line) {
        const line = parseInt(wp.location.line, 10)
        const column = wp.location.column ? parseInt(wp.location.column, 10) : 1
        const type = wp.type || 'waypoint'
        const constraint = wp.constraint?.value || ''
        const hoverMessage = `**Witness Waypoint #${idx}**\n\nType: ${type}${constraint ? `\n\nConstraint: ${constraint}` : ''}`

        // Truncate constraint for inline display (ensure it's a string)
        const constraintStr = constraint ? String(constraint) : ''
        const constraintPreview = constraintStr ? constraintStr.substring(0, 50) + (constraintStr.length > 50 ? '...' : '') : ''
        const inlineText = ` [${idx}] ${type}${constraintPreview ? ': ' + constraintPreview : ''} `

        newDecorations.push({
          range: new monaco.Range(line, column, line, column + 1),
          options: {
            isWholeLine: false,
            className: 'witness-marker-line',
            glyphMarginClassName: 'witness-marker-glyph',
            hoverMessage: { value: hoverMessage },
            before: {
              content: inlineText,
              inlineClassName: 'witness-inline-text',
              cursorStops: monaco.editor.InjectedTextCursorStops.None
            }
          }
        })
      }
    }

    // Apply decorations
    decorationsRef.current = editorRef.current.deltaDecorations(decorationsRef.current, newDecorations)
  }, [witnessData])

  return (
    <Box sx={{ width: '100%', height: '100%', display: 'flex', flexDirection: 'column' }}>
      <EditorToolbar examples={examples} properties={properties} selectedProperty={selectedProperty} mode={mode} modesConfig={modesConfig} safetyResult={safetyResult} verifyRunning={verifyRunning} verificationValid={verificationValid} onSelectExample={onSelectExample} onSelectProperty={onSelectProperty} />
      <Box ref={ref} sx={{ flex: 1, minHeight: 0 }} />
    </Box>
  )
}
