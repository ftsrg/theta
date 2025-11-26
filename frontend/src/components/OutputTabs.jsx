import React, { useState, useEffect } from 'react'
import { Tabs, Tab, Box, Collapse, IconButton, Button } from '@mui/material'
import ExpandMoreIcon from '@mui/icons-material/ExpandMore'
import ChevronRightIcon from '@mui/icons-material/ChevronRight'
import OpenInNewIcon from '@mui/icons-material/OpenInNew'
import DownloadIcon from '@mui/icons-material/Download'
import yaml from 'js-yaml'

export default function OutputTabs({ result, onWitnessAnnotate }) {
  const [tab, setTab] = useState(0)
  const stderr = result ? (result.stderr || '') : ''
  const stdout = result ? (result.stdout || '') : ''
  const generated = Array.isArray(result?.generatedFiles) ? result.generatedFiles : []
  const [openMap, setOpenMap] = useState({})
  const toggle = (p) => setOpenMap(m => ({ ...m, [p]: !m[p] }))

  // Auto-apply witness.yml when it becomes available
  useEffect(() => {
    if (onWitnessAnnotate && generated.length > 0) {
      const witnessFile = generated.find(f => f.path.endsWith('witness.yml'))
      if (witnessFile) {
        try {
          const parsed = yaml.load(witnessFile.content)
          onWitnessAnnotate(parsed)
        } catch (err) {
          console.error('Failed to parse witness YAML:', err)
        }
      }
    }
  }, [generated, onWitnessAnnotate])

  // Download all generated files as zip
  const downloadAllFiles = async () => {
    if (generated.length === 0) return
    
    // Dynamically import JSZip
    const JSZip = (await import('jszip')).default
    const zip = new JSZip()
    
    // Add each file to the zip
    for (const file of generated) {
      zip.file(file.path, file.content || '')
    }
    
    // Generate the zip and trigger download
    const blob = await zip.generateAsync({ type: 'blob' })
    const url = URL.createObjectURL(blob)
    const a = document.createElement('a')
    a.href = url
    a.download = 'generated-files.zip'
    document.body.appendChild(a)
    a.click()
    document.body.removeChild(a)
    URL.revokeObjectURL(url)
  }

  // Open SVG in new tab
  const openSvgInNewTab = (content) => {
    const blob = new Blob([content], { type: 'image/svg+xml' })
    const url = URL.createObjectURL(blob)
    window.open(url, '_blank')
  }

  // Build simple directory tree structure
  const treeRoot = {}
  for (const f of generated) {
    const parts = f.path.split(/\//).filter(Boolean)
    let node = treeRoot
    for (let i = 0; i < parts.length; i++) {
      const part = parts[i]
      if (!node[part]) node[part] = { __children: {} }
      if (i === parts.length - 1) node[part].__file = f
      node = node[part].__children
    }
  }

  function renderNode(obj, base) {
    const entries = Object.keys(obj).sort()
    return entries.map(name => {
      const data = obj[name]
      const file = data.__file
      const hasChildren = Object.keys(data.__children).length > 0
      const relPath = base ? base + '/' + name : name
      const isOpen = !!openMap[relPath]
      const isExpandable = hasChildren || file
      const isSvg = file?.path.endsWith('.svg')

      return (
        <div key={relPath} style={{ marginLeft: base ? 12 : 0 }}>
          <div style={{ display: 'flex', alignItems: 'center' }}>
            {isExpandable && (
              <IconButton size="small" onClick={() => toggle(relPath)} sx={{ p: 0.5, color: '#fff' }}>
                {isOpen ? <ExpandMoreIcon fontSize="inherit" /> : <ChevronRightIcon fontSize="inherit" />}
              </IconButton>
            )}
            {!isExpandable && <span style={{ width: 20 }} />}
            <span
              style={{ cursor: isExpandable ? 'pointer' : 'default', color: file ? '#e0e0e0' : '#9aa0aa' }}
              onClick={() => toggle(relPath)}
            >
              {name}
              {file && ' ' + (file.truncated ? '(truncated)' : '')}
            </span>
            {isSvg && isOpen && (
              <IconButton
                size="small"
                onClick={() => openSvgInNewTab(file.content)}
                sx={{ p: 0.5, ml: 1, color: '#4472c4' }}
                title="Open in new tab"
              >
                <OpenInNewIcon fontSize="small" />
              </IconButton>
            )}
          </div>
          <Collapse in={isOpen} unmountOnExit>
            {file && (
              <>
                {isSvg ? (
                  <div
                    className="output-svg-container"
                    style={{
                      margin: '4px 0 8px',
                      padding: '4px 6px',
                      background: '#1b1f24',
                      border: '1px solid #2a3138',
                      borderRadius: 4,
                      maxWidth: '100%',
                      overflow: 'auto'
                    }}
                  >
                    <div dangerouslySetInnerHTML={{ __html: file.content }} />
                  </div>
                ) : (
                  <pre
                    style={{
                      margin: '4px 0 8px',
                      padding: '4px 6px',
                      background: '#1b1f24',
                      border: '1px solid #2a3138',
                      borderRadius: 4,
                      whiteSpace: 'pre-wrap',
                      color: '#d0d0d0'
                    }}
                  >
                    {file.content || '// empty file'}
                  </pre>
                )}
              </>
            )}
            {hasChildren && renderNode(data.__children, relPath)}
          </Collapse>
        </div>
      )
    })
  }

  return (
    <Box sx={{ height: '100%', display: 'flex', flexDirection: 'column', minHeight: 0 }}>
      <Box sx={{ display: 'flex', alignItems: 'center', background: 'rgb(82, 43, 71)' }}>
        <Tabs
          value={tab}
          onChange={(e, v) => setTab(v)}
          sx={{
            flex: 1,
            minHeight: 36,
            '& .MuiTab-root': { minHeight: 36, textTransform: 'none', color: '#cfd8e6' },
            '& .MuiTab-root.Mui-selected': { color: '#fff' },
            '& .MuiTabs-indicator': { background: 'rgb(251, 139, 36)', height: 2 }
          }}
        >
          <Tab label="Output" />
          <Tab label="Generated Files" />
        </Tabs>
        {tab === 1 && generated.length > 0 && (
          <Button
            size="small"
            startIcon={<DownloadIcon />}
            onClick={downloadAllFiles}
            sx={{
              mr: 1,
              textTransform: 'none',
              color: '#cfd8e6',
              '&:hover': { bgcolor: 'rgba(255, 255, 255, 0.1)' }
            }}
          >
            Download All
          </Button>
        )}
      </Box>
      <Box sx={{ flex: 1, overflow: 'auto', bgcolor: '#0f1115', p: 1, fontFamily: 'monospace', fontSize: 12 }}>
        {tab === 0 && (
          <div style={{ whiteSpace: 'pre-wrap' }}>
            {stderr && <pre style={{ margin: 0, color: '#ff8585', whiteSpace: 'pre-wrap' }}>{stderr}</pre>}
            {stdout && <pre style={{ margin: 0, color: '#ddd', whiteSpace: 'pre-wrap' }}>{stdout}</pre>}
            {!stderr && !stdout && <pre style={{ margin: 0, color: '#555', whiteSpace: 'pre-wrap' }}>// no output</pre>}
          </div>
        )}
        {tab === 1 && (
          <div style={{ whiteSpace: 'normal', fontFamily: 'inherit' }}>
            {generated.length === 0 && !result?.generatedFilesError && (
              <pre style={{ margin: 0, color: '#555' }}>// no generated files</pre>
            )}
            {result?.generatedFilesError && (
              <pre style={{ margin: 0, color: '#ff8585' }}>// error: {result.generatedFilesError}</pre>
            )}
            {generated.length > 0 && renderNode(treeRoot, '')}
          </div>
        )}
      </Box>
    </Box>
  )
}
