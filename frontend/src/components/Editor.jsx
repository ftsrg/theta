import React, { useEffect, useRef } from 'react'
import * as monaco from 'monaco-editor'
import { Box } from '@mui/material'
import EditorToolbar from './EditorToolbar'

export default function Editor({ code, onChange, onPositionChange, examples, properties, onSelectExample }) {
  const ref = useRef(null)
  const editorRef = useRef(null)

  useEffect(() => {
    editorRef.current = monaco.editor.create(ref.current, {
      value: code || '',
      language: 'cpp',
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

  return (
    <Box sx={{ width: '100%', height: '100%', display: 'flex', flexDirection: 'column' }}>
      <EditorToolbar examples={examples} properties={properties} onSelectExample={onSelectExample} />
      <Box ref={ref} sx={{ flex: 1, minHeight: 0 }} />
    </Box>
  )
}
