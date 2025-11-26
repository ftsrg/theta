import React, { useState } from 'react'
import { Box, Button, Popover } from '@mui/material'
import FolderOpenIcon from '@mui/icons-material/FolderOpen'
import DescriptionIcon from '@mui/icons-material/Description'
import ExampleTree from './ExampleTree'

export default function EditorToolbar({ examples = [], properties = [], selectedProperty = 'unreach-call.prp', onSelectExample, onSelectProperty }) {
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
    handleCloseProperties()
  }

  return (
    <Box
      sx={{
        display: 'flex',
        alignItems: 'center',
        gap: 1,
        px: 1,
        py: 0.5,
        bgcolor: '#1b1f24',
        borderBottom: '1px solid #2a3138'
      }}
    >
      {/* Examples Button */}
      <Button
        size="small"
        variant="outlined"
        startIcon={<FolderOpenIcon />}
        onClick={handleOpenExamples}
        sx={{
          textTransform: 'none',
          color: '#cfd8e6',
          borderColor: 'rgba(255, 255, 255, 0.23)',
          '&:hover': {
            borderColor: 'rgba(255, 255, 255, 0.4)',
            bgcolor: 'rgba(255, 255, 255, 0.05)'
          }
        }}
      >
        Examples
      </Button>
      <Popover
        open={openExamples}
        anchorEl={examplesAnchor}
        onClose={handleCloseExamples}
        anchorOrigin={{ vertical: 'bottom', horizontal: 'left' }}
      >
        <Box sx={{ width: 360 }}>
          <ExampleTree examples={examples} onSelect={handleSelectExample} />
        </Box>
      </Popover>

      {/* Property Selector */}
      <Button
        size="small"
        variant="outlined"
        startIcon={<DescriptionIcon />}
        onClick={handleOpenProperties}
        sx={{
          textTransform: 'none',
          color: '#cfd8e6',
          borderColor: 'rgba(255, 255, 255, 0.23)',
          '&:hover': {
            borderColor: 'rgba(255, 255, 255, 0.4)',
            bgcolor: 'rgba(255, 255, 255, 0.05)'
          }
        }}
      >
        Property: {formatPropertyName(selectedProperty)}
      </Button>
      <Popover
        open={openProperties}
        anchorEl={propertiesAnchor}
        onClose={handleCloseProperties}
        anchorOrigin={{ vertical: 'bottom', horizontal: 'left' }}
      >
        <Box sx={{ width: 300, maxHeight: 400, overflow: 'auto' }}>
          {properties.map((prop) => (
            <Box
              key={prop}
              onClick={() => handleSelectProperty(prop)}
              sx={{
                px: 2,
                py: 1,
                cursor: 'pointer',
                bgcolor: prop === selectedProperty ? 'rgba(68, 114, 196, 0.1)' : 'transparent',
                '&:hover': {
                  bgcolor: prop === selectedProperty ? 'rgba(68, 114, 196, 0.2)' : 'rgba(255, 255, 255, 0.05)'
                },
                borderLeft: prop === selectedProperty ? '3px solid rgb(68, 114, 196)' : '3px solid transparent',
                transition: 'all 0.2s'
              }}
            >
              {formatPropertyName(prop)}
            </Box>
          ))}
        </Box>
      </Popover>
    </Box>
  )
}
