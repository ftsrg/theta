import React, { useState, useEffect, useRef } from 'react'
import { AppBar, Toolbar as MuiToolbar, Button, TextField, Autocomplete, Tooltip, Box, Typography, Popover, useMediaQuery } from '@mui/material'
import { useTheme } from '@mui/material/styles'
import FolderOpenIcon from '@mui/icons-material/FolderOpen'
import LockOutlinedIcon from '@mui/icons-material/LockOutlined'
import ExampleTree from './ExampleTree'
import { api } from '../api'

export default function Toolbar({
  examples = [],
  versions = [],
  releases = [],
  signedIn = false,
  onSelectExample,
  onRefreshVersions,
  onRun,
  onRequestLogin,
  onStreamRetrieve,
  onOpenLogin,
  onLogout
}) {
  const theme = useTheme()
  const isNarrow = useMediaQuery('(max-width:1000px)')

  const [selectedRelease, setSelectedRelease] = useState('')
  const [availableJars, setAvailableJars] = useState([])
  const [selectedJar, setSelectedJar] = useState('')
  const [args, setArgs] = useState('--input %in --backend PORTFOLIO')
  const [retrieving, setRetrieving] = useState(false)
  const [shouldWrap, setShouldWrap] = useState(false)

  const [examplesAnchor, setExamplesAnchor] = useState(null)
  const openExamples = Boolean(examplesAnchor)

  // initial auto-select latest release
  useEffect(() => {
    if (releases.length > 0 && !selectedRelease) setSelectedRelease(releases[0].tag)
  }, [releases, selectedRelease])

  // update jars when release changes
  useEffect(() => {
    const rel = releases.find(r => r.tag === selectedRelease)
     const jars = rel ? rel.assets.map(a => a.name) : []
     setAvailableJars(jars)
     const xcfaJar = jars.find(j => j.includes("xcfa"))
     setSelectedJar(xcfaJar || '')
  }, [selectedRelease, releases])

  const currentVersion = versions.find(v => v.name === selectedRelease)
  const jarRetrieved = !!(selectedJar && currentVersion && currentVersion.jars.includes(selectedJar))

  // simple viewport-based wrap: mobile when viewport < 1000px
  useEffect(() => {
    setShouldWrap(isNarrow)
  }, [isNarrow])

  const doRetrieve = async () => {
    if (!selectedRelease || !selectedJar) return
    if (!signedIn) {
      onRequestLogin && onRequestLogin(selectedRelease)
      return
    }
    if (onStreamRetrieve) {
      onStreamRetrieve(selectedRelease, selectedJar, () => {
        onRefreshVersions && onRefreshVersions()
      })
      return
    }
    setRetrieving(true)
    try {
      await api.post('/api/theta/retrieve', { version: selectedRelease, assetName: selectedJar })
      onRefreshVersions && onRefreshVersions()
    } catch (e) {
      console.error(e)
    } finally {
      setRetrieving(false)
    }
  }

  const run = () => {
    const argList = args.split(/\s+/).filter(Boolean)
    onRun({ binaryName: 'theta-jar', args: argList, thetaVersion: selectedRelease, jarFile: selectedJar })
  }

  const handleOpenExamples = (e) => setExamplesAnchor(e.currentTarget)
  const handleCloseExamples = () => setExamplesAnchor(null)
  const handleSelectExample = (path) => {
    onSelectExample(path)
    handleCloseExamples()
  }

  return (
    <AppBar position="static" className="app-toolbar" elevation={0}>
      <MuiToolbar
        sx={{
          flexWrap: shouldWrap ? 'wrap' : 'nowrap',
          alignItems: shouldWrap ? 'flex-start' : 'center',
          gap: shouldWrap ? 0.5 : 1,
          minHeight: shouldWrap ? 'auto' : 56,
          px: shouldWrap ? 1 : undefined
        }}
      >
        {/* Logo */}
        <Box sx={{ display: 'flex', alignItems: 'center', gap: 1, mr: 2 }}>
          <a
            href="https://theta.mit.bme.hu"
            target="_blank"
            rel="noopener noreferrer"
            style={{ display: 'flex', alignItems: 'center', height: 32 }}
          >
            <img
              src="https://raw.githubusercontent.com/ftsrg/theta/master/doc/theta-logo.svg"
              alt="Theta"
              style={{ height: 32, filter: 'brightness(0) invert(1)' }}
            />
          </a>
        </Box>

        {/* Title */}
        <Typography variant="h6" sx={{ fontSize: 16, mr: 2, whiteSpace: 'nowrap' }}>
          Verification Demo
        </Typography>

        {/* Login/Logout - in mobile mode, place right after title */}
        {shouldWrap && (
          !signedIn ? (
            <Button color="inherit" onClick={onOpenLogin} sx={{ ml: 'auto', flexShrink: 0 }}>
              Login
            </Button>
          ) : (
            <Button color="inherit" onClick={onLogout} sx={{ ml: 'auto', flexShrink: 0 }}>
              Sign out
            </Button>
          )
        )}

        {/* Examples Button */}
        <Button 
          size="small" 
          color="inherit" 
          startIcon={<FolderOpenIcon />} 
          onClick={handleOpenExamples}
          sx={{
            order: shouldWrap ? 1 : 0,
            flexBasis: shouldWrap ? '100%' : 'auto'
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
    
        {/* Release Selector */}
        <Autocomplete
        size="small"
        options={releases.map(r => r.tag)}
        value={selectedRelease}
        onChange={(e, val) => setSelectedRelease(val || '')}
        sx={{
            flexGrow: shouldWrap ? 0 : 1,
            width: shouldWrap ? '100%' : 'auto',
            maxWidth: shouldWrap ? 'none' : 200,
            '& .MuiOutlinedInput-root': {
            bgcolor: 'transparent',
            borderRadius: 1,
            px: 1,
            color: '#fff',
            '& fieldset': { display: 'none' },
            '& input': {
                py: 1,
                color: '#fff',
                '::placeholder': { color: 'rgba(255,255,255,0.6)' },
                pr: 3
            },
            '& .MuiAutocomplete-endAdornment svg': { color: '#fff' }
            }
        }}
        disableClearable
        renderInput={(params) => <TextField {...params} placeholder="Release" variant="outlined" />}
        />

        {/* Jar Selector */}
        <Autocomplete
        size="small"
        options={availableJars}
        value={selectedJar}
        onChange={(e, val) => setSelectedJar(val || '')}
        sx={{
            flexGrow: shouldWrap ? 0 : 1,
            width: shouldWrap ? '100%' : 'auto',
            maxWidth: shouldWrap ? 'none' : 350,
            '& .MuiOutlinedInput-root': {
            bgcolor: 'transparent',
            borderRadius: 1,
            px: 1,
            color: '#fff',
            '& fieldset': { display: 'none' },
            '& input': {
                py: 1,
                color: '#fff',
                '::placeholder': { color: 'rgba(255,255,255,0.6)' },
                pr: 3
            },
            '& .MuiAutocomplete-endAdornment svg': { color: '#fff' }
            }
        }}
        disableClearable
        renderInput={(params) => <TextField {...params} placeholder="Jar" variant="outlined" />}
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
                disabled={retrieving || !selectedRelease || !selectedJar}
                sx={{
                borderColor: 'rgb(68, 114, 196)',
                color: 'rgb(68, 114, 196)',
                '&:hover': {
                    borderColor: 'rgb(68, 114, 196)',
                    bgcolor: 'rgba(68, 114, 196, 0.1)'
                }
                }}
            >
                {retrieving ? 'Retrieving...' : 'Retrieve'}
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
            flexGrow: 1,
            width: shouldWrap ? '100%' : 'auto',
            '& .MuiOutlinedInput-root': {
            bgcolor: 'transparent',
            borderRadius: 1,
            px: 1,
            color: '#fff',
            '& fieldset': { display: 'none' },
            '& input': {
                py: 1,
                color: '#fff',
                '::placeholder': { color: 'rgba(255,255,255,0.6)' }
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
            bgcolor: 'rgb(112, 173, 71)',
            '&:hover': { bgcolor: 'rgb(92, 153, 51)' }
            }}
        >
            Run
        </Button>
        )}

        {/* Login/Logout - in desktop mode, place at the end */}
        {!shouldWrap && (
          !signedIn ? (
            <Button color="inherit" onClick={onOpenLogin} sx={{ ml: 'auto', flexShrink: 0 }}>
              Login
            </Button>
          ) : (
            <Button color="inherit" onClick={onLogout} sx={{ ml: 'auto', flexShrink: 0 }}>
              Sign out
            </Button>
          )
        )}
      </MuiToolbar>
    </AppBar>
  )
}
