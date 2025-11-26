import React from 'react'
import { Box, Button } from '@mui/material'
import OutputToolbar from './OutputToolbar'
import OutputTabs from './OutputTabs'

export default function OutputPanel({
  result,
  versions,
  releases,
  signedIn,
  verifyRunning,
  selectedProperty,
  presets = [],
  jar = '',
  onRun,
  onRefreshVersions,
  onRequestLogin,
  onStreamRetrieve,
  onJarContextChange,
  onCancelVerification,
  onWitnessAnnotate
}) {
  return (
    <Box sx={{ width: '100%', height: '100%', display: 'flex', flexDirection: 'column' }}>
      <OutputToolbar
        versions={versions}
        releases={releases}
        signedIn={signedIn}
        selectedProperty={selectedProperty}
        presets={presets}
        jar={jar}
        onJarContextChange={onJarContextChange}
        onRun={onRun}
        onRefreshVersions={onRefreshVersions}
        onRequestLogin={onRequestLogin}
        onStreamRetrieve={onStreamRetrieve}
      />
      {verifyRunning && (
        <Box
          sx={{
            p: 0.5,
            display: 'flex',
            justifyContent: 'flex-end',
            bgcolor: '#1b1f24',
            borderBottom: '1px solid #2a3138'
          }}
        >
          <Button size="small" color="error" variant="outlined" onClick={onCancelVerification}>
            Cancel verification
          </Button>
        </Box>
      )}
      <Box sx={{ flex: 1, minHeight: 0 }}>
        <OutputTabs result={result} onWitnessAnnotate={onWitnessAnnotate} />
      </Box>
    </Box>
  )
}
