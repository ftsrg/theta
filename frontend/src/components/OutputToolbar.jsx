import React, { useState, useEffect, useMemo, useRef } from 'react'
import { Box, Button, TextField, Autocomplete, Tooltip } from '@mui/material'
import LockOutlinedIcon from '@mui/icons-material/LockOutlined'

export default function OutputToolbar({
  versions = [],
  releases = [],
  signedIn = false,
  selectedProperty = 'unreach-call.prp',
  presets = [],
  jar = '',
  selectedRelease: controlledRelease,
  selectedPreset: controlledPreset,
  args: controlledArgs,
  onJarContextChange,
  onRun,
  onRefreshVersions,
  onRequestLogin,
  onStreamRetrieve,
  onReleaseChange,
  onPresetChange,
  onArgsChange
}) {
  // Use controlled props if provided, otherwise maintain local state
  const [localRelease, setLocalRelease] = useState('')
  const [localArgs, setLocalArgs] = useState('--input %in --property %prop --backend PORTFOLIO')
  const [localPresetName, setLocalPresetName] = useState('')
  
  // Check if controlled props are provided (even if empty string)
  const hasControlledRelease = controlledRelease !== undefined
  const hasControlledPreset = controlledPreset !== undefined
  const hasControlledArgs = controlledArgs !== undefined
  
  const selectedRelease = hasControlledRelease ? controlledRelease : localRelease
  const args = hasControlledArgs ? controlledArgs : localArgs
  const selectedPresetName = hasControlledPreset ? controlledPreset : localPresetName
  
  const setSelectedRelease = (val) => {
    if (onReleaseChange) onReleaseChange(val)
    else setLocalRelease(val)
  }
  const setArgs = (val) => {
    if (onArgsChange) onArgsChange(val)
    else setLocalArgs(val)
  }
  const setSelectedPresetName = (val) => {
    if (onPresetChange) onPresetChange(val)
    else setLocalPresetName(val)
  }

  const XCFA_DEFAULT = '--input %in --property %prop --backend PORTFOLIO'
  const XSTS_DEFAULT = 'CEGAR --model %in --inline-property %prop'

  // Initialize release from releases list if not already set
  const didRestoreRelease = useRef(false)
  useEffect(() => {
    if (didRestoreRelease.current) return
    if (releases.length === 0) return
    // Only set default if no release is already selected (from saved config)
    if (!selectedRelease && !hasControlledRelease && releases[0]) {
      setSelectedRelease(releases[0].tag)
    }
    didRestoreRelease.current = true
  }, [releases, selectedRelease, hasControlledRelease])

  // No jar selector: jar derived from selected preset

  const currentVersion = versions.find(v => v.name === selectedRelease)
  const filteredPresets = useMemo(() => presets || [], [presets])
  const selectedPreset = useMemo(() => filteredPresets.find(p => p.name === selectedPresetName) || null, [filteredPresets, selectedPresetName])
  const selectedJar = jar
  const jarRetrieved = !!(selectedJar && currentVersion && currentVersion.jars.includes(selectedJar))

  // Auto-select first preset only if we don't have a controlled value
  useEffect(() => {
    const names = filteredPresets.map(p => p.name)
    
    if (names.length === 0) {
      return
    }
    
    // If we have a controlled preset from parent (saved config), use it (even if empty for Custom)
    if (hasControlledPreset) {
      return
    }
    
    // Only auto-select if the current selection is invalid
    if (!selectedPresetName || !names.includes(selectedPresetName)) {
      setSelectedPresetName(names[0])
      const preset0 = filteredPresets[0]
      setArgs((preset0 && preset0.args) || XCFA_DEFAULT)
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [filteredPresets.map(p => p.name).join('|')])

  useEffect(() => {
    if (onJarContextChange) onJarContextChange({ selectedRelease })
  }, [selectedRelease, onJarContextChange])

  useEffect(() => {
    const isDefaultLike = (val) => !val || val.trim() === '' || val.trim() === XCFA_DEFAULT || val.trim() === XSTS_DEFAULT
    if (isDefaultLike(args) && !selectedPresetName) setArgs(XCFA_DEFAULT)
  }, [selectedPresetName])

  const doRetrieve = () => {
    if (!selectedRelease || !selectedJar) return
    if (!signedIn) {
      onRequestLogin && onRequestLogin(selectedRelease)
      return
    }
    if (onStreamRetrieve) {
      onStreamRetrieve(selectedRelease, selectedJar, () => {
        onRefreshVersions && onRefreshVersions()
      })
    }
  }

  // Removed auto-retrieve: user must click the Retrieve button to start download

  const run = () => {
    const effectiveArgs = selectedPresetName
      ? (selectedPreset?.args || '')
      : args
    const argList = effectiveArgs.split(/\s+/).filter(Boolean).map(arg => (arg === '%prop' ? selectedProperty : arg))
    onRun({ binaryName: 'theta-jar', args: argList, thetaVersion: selectedRelease, jarFile: selectedJar })
  }

  return (
    <Box sx={{ px: 1, py: 0.5, bgcolor: '#1b1f24', borderBottom: '1px solid #2a3138' }}>
      <Box sx={{ display: 'flex', alignItems: 'center', gap: 1, flexWrap: 'wrap' }}>
        <Autocomplete
          size="small"
          options={releases.map(r => r.tag)}
          value={selectedRelease}
          onChange={(e, val) => setSelectedRelease(val || '')}
          sx={{
            flexGrow: 1,
            minWidth: 150,
            maxWidth: 200,
            '& .MuiOutlinedInput-root': {
              bgcolor: 'transparent',
              color: '#cfd8e6',
              '& fieldset': { borderColor: 'rgba(255, 255, 255, 0.23)' },
              '&:hover fieldset': { borderColor: 'rgba(255, 255, 255, 0.4)' },
              '&.Mui-focused fieldset': { borderColor: 'rgb(68, 114, 196)' },
              '& input': { py: 0.75, color: '#cfd8e6' },
              '& .MuiAutocomplete-endAdornment svg': { color: '#cfd8e6' }
            }
          }}
          disableClearable
          renderInput={(params) => (
            <TextField {...params} placeholder="Release" variant="outlined" />
          )}
        />

        {/* Jar selector removed: jar derived from preset */}

        {!jarRetrieved && selectedRelease && selectedJar && (
          <Tooltip title={signedIn ? 'Retrieve jar' : 'Sign in required – click to login'}>
            <span>
              <Button
                variant="outlined"
                size="small"
                onClick={doRetrieve}
                startIcon={!signedIn ? <LockOutlinedIcon /> : undefined}
                disabled={!selectedRelease || !selectedJar}
                sx={{ textTransform: 'none', borderColor: 'rgb(68, 114, 196)', color: 'rgb(68, 114, 196)', '&:hover': { borderColor: 'rgb(68, 114, 196)', bgcolor: 'rgba(68, 114, 196, 0.1)' } }}
              >
                Retrieve
              </Button>
            </span>
          </Tooltip>
        )}

        <Autocomplete
          size="small"
          options={filteredPresets.map(p => p.name).concat(['Custom'])}
          value={selectedPresetName || 'Custom'}
          onChange={(e, val) => {
            const name = val || 'Custom'
            setSelectedPresetName(name === 'Custom' ? '' : name)
            const preset = filteredPresets.find(p => p.name === name)
            if (preset && preset.args) setArgs(preset.args)
          }}
          sx={{
            flexGrow: 1,
            minWidth: 180,
            maxWidth: 220,
            '& .MuiOutlinedInput-root': {
              bgcolor: 'transparent',
              color: '#cfd8e6',
              '& fieldset': { borderColor: 'rgba(255, 255, 255, 0.23)' },
              '&:hover fieldset': { borderColor: 'rgba(255, 255, 255, 0.4)' },
              '&.Mui-focused fieldset': { borderColor: 'rgb(68, 114, 196)' },
              '& input': { py: 0.75, color: '#cfd8e6' },
              '& .MuiAutocomplete-endAdornment svg': { color: '#cfd8e6' }
            }
          }}
          disableClearable
          renderInput={(params) => (
            <TextField {...params} placeholder="Config" variant="outlined" />
          )}
        />

        {selectedRelease && selectedJar && jarRetrieved && (
          <Button variant="contained" size="small" onClick={run} sx={{ textTransform: 'none', bgcolor: 'rgb(112, 173, 71)' }}>
            Run
          </Button>
        )}
      </Box>

      {!selectedPresetName && (
        <Box sx={{ display: 'flex', alignItems: 'center', gap: 1, mt: 1 }}>
          <TextField
            size="small"
            placeholder={'Args'}
            value={args}
            onChange={e => setArgs(e.target.value)}
            sx={{
              flexGrow: 1,
              minWidth: 200,
              '& .MuiOutlinedInput-root': {
                bgcolor: 'transparent',
                color: '#cfd8e6',
                '& fieldset': { borderColor: 'rgba(255, 255, 255, 0.23)' },
                '&:hover fieldset': { borderColor: 'rgba(255, 255, 255, 0.4)' },
                '&.Mui-focused fieldset': { borderColor: 'rgb(68, 114, 196)' },
                '& input': { py: 0.75, color: '#cfd8e6' }
              }
            }}
            variant="outlined"
          />
        </Box>
      )}
    </Box>
  )
}
