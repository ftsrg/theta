import React, { useState, useEffect, useMemo, useRef } from 'react'
import { Box, Button, TextField, Autocomplete, Tooltip } from '@mui/material'
import LockOutlinedIcon from '@mui/icons-material/LockOutlined'

export default function OutputToolbar({
  versions = [],
  releases = [],
  signedIn = false,
  selectedProperty = 'unreach-call.prp',
  presets = [],
  onJarContextChange,
  onRun,
  onRefreshVersions,
  onRequestLogin,
  onStreamRetrieve
}) {
  const [selectedRelease, setSelectedRelease] = useState('')
  const [availableJars, setAvailableJars] = useState([])
  const [selectedJar, setSelectedJar] = useState('')
  const [args, setArgs] = useState('--input %in --property %prop --backend PORTFOLIO')
  const [selectedPresetName, setSelectedPresetName] = useState('')

  const XCFA_DEFAULT = '--input %in --property %prop --backend PORTFOLIO'
  const XSTS_DEFAULT = 'CEGAR --model %in --inline-property %prop'

  // Restore release from localStorage only once after releases load
  const didRestoreRelease = useRef(false)
  useEffect(() => {
    if (didRestoreRelease.current) return
    if (releases.length === 0) return
    const saved = localStorage.getItem('theta.selectedRelease')
    const tags = releases.map(r => r.tag)
    if (saved && tags.includes(saved)) {
      setSelectedRelease(saved)
    } else if (!selectedRelease) {
      setSelectedRelease(releases[0].tag)
    }
    didRestoreRelease.current = true
  }, [releases])

  // Update jars when release changes and restore saved jar if available
  useEffect(() => {
    const rel = releases.find(r => r.tag === selectedRelease)
    const jars = rel ? rel.assets.map(a => a.name) : []
    setAvailableJars(jars)
    const savedJar = localStorage.getItem('theta.selectedJar')
    if (savedJar && jars.includes(savedJar)) {
      setSelectedJar(savedJar)
    } else {
      const xcfaJar = jars.find(j => j.includes('xcfa'))
      setSelectedJar(xcfaJar || '')
    }
  }, [selectedRelease, releases])

  const currentVersion = versions.find(v => v.name === selectedRelease)
  const jarRetrieved = !!(selectedJar && currentVersion && currentVersion.jars.includes(selectedJar))

  const isXsts = useMemo(() => (selectedJar || '').toLowerCase().includes('xsts'), [selectedJar])
  const filteredPresets = useMemo(() => {
    const t = isXsts ? 'xsts' : 'xcfa'
    return (presets || []).filter(p => (p.type || '') === t)
  }, [presets, isXsts])

  // Restore preset from localStorage if valid for current jar type; else first preset or Custom
  useEffect(() => {
    const names = filteredPresets.map(p => p.name)
    const savedPreset = localStorage.getItem('theta.selectedPresetName')
    if (names.length > 0) {
      if (savedPreset && names.includes(savedPreset)) {
        setSelectedPresetName(savedPreset)
        const preset = filteredPresets.find(p => p.name === savedPreset)
        setArgs((preset && preset.args) || (isXsts ? XSTS_DEFAULT : XCFA_DEFAULT))
      } else if (!selectedPresetName || !names.includes(selectedPresetName)) {
        setSelectedPresetName(names[0])
        const preset0 = filteredPresets[0]
        setArgs((preset0 && preset0.args) || (isXsts ? XSTS_DEFAULT : XCFA_DEFAULT))
      }
    } else {
      setSelectedPresetName('')
      const savedCustomArgs = localStorage.getItem('theta.customArgs')
      setArgs(savedCustomArgs || (isXsts ? XSTS_DEFAULT : XCFA_DEFAULT))
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [isXsts, filteredPresets.map(p => p.name).join('|')])

  useEffect(() => {
    if (onJarContextChange) onJarContextChange({ selectedRelease, selectedJar, isXsts })
  }, [selectedRelease, selectedJar, isXsts, onJarContextChange])

  // Persist release/jar/preset/args selections
  useEffect(() => {
    if (selectedRelease) localStorage.setItem('theta.selectedRelease', selectedRelease)
  }, [selectedRelease])
  useEffect(() => {
    if (selectedJar) localStorage.setItem('theta.selectedJar', selectedJar)
  }, [selectedJar])
  useEffect(() => {
    // Empty string represents Custom
    localStorage.setItem('theta.selectedPresetName', selectedPresetName || '')
  }, [selectedPresetName])
  useEffect(() => {
    // Only persist custom args (when Custom selected)
    if (!selectedPresetName) localStorage.setItem('theta.customArgs', args)
  }, [args, selectedPresetName])

  useEffect(() => {
    const isDefaultLike = (val) => !val || val.trim() === '' || val.trim() === XCFA_DEFAULT || val.trim() === XSTS_DEFAULT
    if (isDefaultLike(args) && !selectedPresetName) setArgs(isXsts ? XSTS_DEFAULT : XCFA_DEFAULT)
  }, [isXsts, selectedPresetName])

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

  useEffect(() => {
    if (!selectedRelease || !selectedJar) return
    if (isXsts && !jarRetrieved) {
      if (signedIn) doRetrieve()
      else onRequestLogin && onRequestLogin(selectedRelease)
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [isXsts, selectedRelease, selectedJar])

  const run = () => {
    const effectiveArgs = selectedPresetName
      ? (filteredPresets.find(p => p.name === selectedPresetName)?.args || '')
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

        <Autocomplete
          size="small"
          options={availableJars}
          value={selectedJar}
          onChange={(e, val) => setSelectedJar(val || '')}
          sx={{
            flexGrow: 2,
            minWidth: 200,
            maxWidth: 350,
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
            <TextField {...params} placeholder="Jar" variant="outlined" />
          )}
        />

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
            // Persist selection
            localStorage.setItem('theta.selectedPresetName', name === 'Custom' ? '' : name)
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
