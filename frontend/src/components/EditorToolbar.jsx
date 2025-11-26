import React, { useState, useEffect } from 'react'
import { Box, Button, Popover, TextField, Tooltip } from '@mui/material'
import FolderOpenIcon from '@mui/icons-material/FolderOpen'
import DescriptionIcon from '@mui/icons-material/Description'
import CheckCircleIcon from '@mui/icons-material/CheckCircle'
import CancelIcon from '@mui/icons-material/Cancel'
import HelpOutlineIcon from '@mui/icons-material/HelpOutline'
import ExampleTree from './ExampleTree'

export default function EditorToolbar({ examples = [], properties = [], selectedProperty = 'unreach-call.prp', isXsts = false, safetyResult = '', verifyRunning = false, verificationValid = false, onSelectExample, onSelectProperty }) {
  const [examplesAnchor, setExamplesAnchor] = useState(null)
  const [propertiesAnchor, setPropertiesAnchor] = useState(null)
  
  const openExamples = Boolean(examplesAnchor)
  const openProperties = Boolean(propertiesAnchor)
  
  // Format property names for display (remove .prp and convert to title case)
  const formatPropertyName = (prop) => {
    return prop
      .replace('.prp', '')
      .split('-')
      .map(word => word.charAt(0).toUpperCase() + word.slice(1))
      .join(' ')
  }

  const handleOpenExamples = (e) => setExamplesAnchor(e.currentTarget)
  const handleCloseExamples = () => setExamplesAnchor(null)
  const handleSelectExample = (path) => {
    onSelectExample(path)
    handleCloseExamples()
  }

  const handleOpenProperties = (e) => setPropertiesAnchor(e.currentTarget)
  const handleCloseProperties = () => setPropertiesAnchor(null)
  const handleSelectProperty = (prop) => {
    onSelectProperty(prop)
    // Persist selected property (xcfa case)
    try { localStorage.setItem('theta.selectedProperty', prop) } catch {}
    handleCloseProperties()
  }

  // Restore previously selected property on load
  useEffect(() => {
    const saved = localStorage.getItem('theta.selectedProperty')
    if (!saved) return
    if (!isXsts) {
      // xcfa: only apply if still in list
      if (properties.includes(saved) && saved !== selectedProperty) {
        onSelectProperty && onSelectProperty(saved)
      }
    } else {
      // xsts: any text is acceptable
      if (saved !== selectedProperty) {
        onSelectProperty && onSelectProperty(saved)
      }
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [isXsts, properties.join('|')])

  // Determine status icon and text (only show after verification completes)
  const renderSafetyStatus = () => {
    if (verifyRunning || !verificationValid) return null
    let icon = null
    let text = ''
    if (safetyResult === 'safe') { icon = <CheckCircleIcon sx={{ color:'#70ad47', fontSize:20 }} />; text = 'property holds' }
    else if (safetyResult === 'unsafe') { icon = <CancelIcon sx={{ color:'#c0504d', fontSize:20 }} />; text = 'property does not hold' }
    else { icon = <HelpOutlineIcon sx={{ color:'#9e9e9e', fontSize:20 }} />; text = 'unknown' }
    return (
      <Box sx={{ display:'flex', alignItems:'center', gap:0.75, ml:2, pr:0.5 }}>
        {icon}
        <Box sx={{ fontSize:12, color:'#cfd8e6', fontWeight:500 }}>{text}</Box>
      </Box>
    )
  }

  return (
    <Box sx={{ display:'flex', alignItems:'center', justifyContent:'space-between', px:1, py:0.5, bgcolor:'#1b1f24', borderBottom:'1px solid #2a3138' }}>
      <Box sx={{ display:'flex', alignItems:'center', gap:1 }}>
        <Button
          size="small"
          variant="outlined"
          startIcon={<FolderOpenIcon />}
          onClick={handleOpenExamples}
          sx={{
            textTransform: 'none',
            color: '#cfd8e6',
            borderColor: 'rgba(255, 255, 255, 0.23)',
            '&:hover': { borderColor: 'rgba(255, 255, 255, 0.4)', bgcolor: 'rgba(255, 255, 255, 0.05)' }
          }}
        >Examples</Button>
        <Popover open={openExamples} anchorEl={examplesAnchor} onClose={handleCloseExamples} anchorOrigin={{ vertical:'bottom', horizontal:'left' }}>
          <Box sx={{ width:360 }}><ExampleTree examples={examples} onSelect={handleSelectExample} /></Box>
        </Popover>
        {!isXsts ? (
          <>
            <Button
              size="small"
              variant="outlined"
              startIcon={<DescriptionIcon />}
              onClick={handleOpenProperties}
              sx={{
                textTransform: 'none',
                color: '#cfd8e6',
                borderColor: 'rgba(255, 255, 255, 0.23)',
                '&:hover': { borderColor: 'rgba(255, 255, 255, 0.4)', bgcolor: 'rgba(255, 255, 255, 0.05)' }
              }}
            >Property: {formatPropertyName(selectedProperty)}</Button>
            <Popover open={openProperties} anchorEl={propertiesAnchor} onClose={handleCloseProperties} anchorOrigin={{ vertical:'bottom', horizontal:'left' }}>
              <Box sx={{ width:300, maxHeight:400, overflow:'auto' }}>
                {properties.map((prop) => (
                  <Box
                    key={prop}
                    onClick={() => handleSelectProperty(prop)}
                    sx={{
                      px:2, py:1, cursor:'pointer',
                      bgcolor: prop === selectedProperty ? 'rgba(68,114,196,0.1)' : 'transparent',
                      '&:hover': { bgcolor: prop === selectedProperty ? 'rgba(68,114,196,0.2)' : 'rgba(255,255,255,0.05)' },
                      borderLeft: prop === selectedProperty ? '3px solid rgb(68,114,196)' : '3px solid transparent',
                      transition:'all 0.2s'
                    }}
                  >{formatPropertyName(prop)}</Box>
                ))}
              </Box>
            </Popover>
          </>
        ) : (
          <Tooltip title="e.g., x > 5">
            <TextField
              size="small"
              placeholder="x > 5"
              value={selectedProperty || ''}
              onChange={(e) => { const val=e.target.value; onSelectProperty && onSelectProperty(val); try { localStorage.setItem('theta.selectedProperty', val) } catch {} }}
              sx={{ width:260, '& .MuiOutlinedInput-root': { bgcolor:'transparent', color:'#cfd8e6', '& fieldset': { borderColor:'rgba(255,255,255,0.23)' }, '&:hover fieldset': { borderColor:'rgba(255,255,255,0.4)' }, '&.Mui-focused fieldset': { borderColor:'rgb(68,114,196)' }, '& input': { py:0.75, color:'#cfd8e6' } } }}
              variant="outlined"
            />
          </Tooltip>
        )}
      </Box>
      {renderSafetyStatus()}
    </Box>
  )
}
