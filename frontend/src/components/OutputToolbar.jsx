import React, { useState, useEffect } from 'react'
import { Box, Button, TextField, Autocomplete, Tooltip } from '@mui/material'
import LockOutlinedIcon from '@mui/icons-material/LockOutlined'

export default function OutputToolbar({
  versions = [],
  releases = [],
  signedIn = false,
  selectedProperty = 'unreach-call.prp',
  onRun,
  onRefreshVersions,
  onRequestLogin,
  onStreamRetrieve
}) {
  const [selectedRelease, setSelectedRelease] = useState('')
  const [availableJars, setAvailableJars] = useState([])
  const [selectedJar, setSelectedJar] = useState('')
  const [args, setArgs] = useState('--input %in --property %prop --backend PORTFOLIO')

  // Auto-select latest release
  useEffect(() => {
    if (releases.length > 0 && !selectedRelease) {
      setSelectedRelease(releases[0].tag)
    }
  }, [releases, selectedRelease])

  // Update jars when release changes
  useEffect(() => {
    const rel = releases.find(r => r.tag === selectedRelease)
    const jars = rel ? rel.assets.map(a => a.name) : []
    setAvailableJars(jars)
    const xcfaJar = jars.find(j => j.includes('xcfa'))
    setSelectedJar(xcfaJar || '')
  }, [selectedRelease, releases])

  const currentVersion = versions.find(v => v.name === selectedRelease)
  const jarRetrieved = !!(selectedJar && currentVersion && currentVersion.jars.includes(selectedJar))

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

  const run = () => {
    const argList = args.split(/\s+/).filter(Boolean).map(arg => 
      arg === '%prop' ? selectedProperty : arg
    )
    onRun({
      binaryName: 'theta-jar',
      args: argList,
      thetaVersion: selectedRelease,
      jarFile: selectedJar
    })
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
        borderBottom: '1px solid #2a3138',
        flexWrap: 'wrap'
      }}
    >
      {/* Release Selector */}
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
            '& fieldset': {
              borderColor: 'rgba(255, 255, 255, 0.23)'
            },
            '&:hover fieldset': {
              borderColor: 'rgba(255, 255, 255, 0.4)'
            },
            '&.Mui-focused fieldset': {
              borderColor: 'rgb(68, 114, 196)'
            },
            '& input': {
              py: 0.75,
              color: '#cfd8e6'
            },
            '& .MuiAutocomplete-endAdornment svg': {
              color: '#cfd8e6'
            }
          }
        }}
        disableClearable
        renderInput={(params) => (
          <TextField {...params} placeholder="Release" variant="outlined" />
        )}
      />

      {/* Jar Selector */}
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
            '& fieldset': {
              borderColor: 'rgba(255, 255, 255, 0.23)'
            },
            '&:hover fieldset': {
              borderColor: 'rgba(255, 255, 255, 0.4)'
            },
            '&.Mui-focused fieldset': {
              borderColor: 'rgb(68, 114, 196)'
            },
            '& input': {
              py: 0.75,
              color: '#cfd8e6'
            },
            '& .MuiAutocomplete-endAdornment svg': {
              color: '#cfd8e6'
            }
          }
        }}
        disableClearable
        renderInput={(params) => (
          <TextField {...params} placeholder="Jar" variant="outlined" />
        )}
      />

      {/* Retrieve Button */}
      {!jarRetrieved && selectedRelease && selectedJar && (
        <Tooltip title={signedIn ? 'Retrieve jar' : 'Sign in required – click to login'}>
          <span>
            <Button
              variant="outlined"
              size="small"
              onClick={doRetrieve}
              startIcon={!signedIn ? <LockOutlinedIcon /> : undefined}
              disabled={!selectedRelease || !selectedJar}
              sx={{
                textTransform: 'none',
                borderColor: 'rgb(68, 114, 196)',
                color: 'rgb(68, 114, 196)',
                '&:hover': {
                  borderColor: 'rgb(68, 114, 196)',
                  bgcolor: 'rgba(68, 114, 196, 0.1)'
                }
              }}
            >
              Retrieve
            </Button>
          </span>
        </Tooltip>
      )}

      {/* Args Input */}
      <TextField
        size="small"
        placeholder="Args"
        value={args}
        onChange={e => setArgs(e.target.value)}
        sx={{
          flexGrow: 3,
          minWidth: 200,
          '& .MuiOutlinedInput-root': {
            bgcolor: 'transparent',
            color: '#cfd8e6',
            '& fieldset': {
              borderColor: 'rgba(255, 255, 255, 0.23)'
            },
            '&:hover fieldset': {
              borderColor: 'rgba(255, 255, 255, 0.4)'
            },
            '&.Mui-focused fieldset': {
              borderColor: 'rgb(68, 114, 196)'
            },
            '& input': {
              py: 0.75,
              color: '#cfd8e6'
            }
          }
        }}
        variant="outlined"
      />

      {/* Run Button */}
      {selectedRelease && selectedJar && jarRetrieved && (
        <Button
          variant="contained"
          size="small"
          onClick={run}
          sx={{
            textTransform: 'none',
            bgcolor: 'rgb(112, 173, 71)',
            '&:hover': { bgcolor: 'rgb(92, 153, 51)' }
          }}
        >
          Run
        </Button>
      )}
    </Box>
  )
}
