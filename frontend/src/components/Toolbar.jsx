import React from 'react'
import { AppBar, Toolbar as MuiToolbar, Button, Box, Typography, IconButton, Autocomplete, TextField } from '@mui/material'
import GitHubIcon from '@mui/icons-material/GitHub'
import SaveAltIcon from '@mui/icons-material/SaveAlt'
import FolderOpenIcon from '@mui/icons-material/FolderOpen'
import LinkIcon from '@mui/icons-material/Link'

export default function Toolbar({ signedIn = false, onOpenLogin, onLogout, mode = 'C', modesConfig = {}, onChangeMode, onSaveConfig, onLoadConfig, onCopyLink }) {
  return (
    <AppBar position="static" className="app-toolbar" elevation={0} sx={{ backgroundColor: `var(--${(modesConfig[mode]?.color)||'ftsrg-accent-blue'}) !important` }}>
      <MuiToolbar sx={{ minHeight: 56, gap: 2 }}>
        {/* Logo */}
        <Box sx={{ display: 'flex', alignItems: 'center', gap: 1 }}>
          <a
            href="/"
            style={{ display: 'flex', alignItems: 'center', height: 32 }}
          >
            <img
              src="https://raw.githubusercontent.com/ftsrg/theta/master/doc/theta-logo.svg"
              alt="Theta"
              style={{ height: 32, filter: 'brightness(0) invert(1)' }}
            />
          </a>
        </Box>

        {/* GitHub Icon */}
        <IconButton
          color="inherit"
          component="a"
          href="https://github.com/ftsrg/theta"
          target="_blank"
          rel="noopener noreferrer"
          sx={{ p: 0.5 }}
        >
          <GitHubIcon />
        </IconButton>

        {/* Title + Mode Selector */}
        <Box sx={{ display:'flex', alignItems:'center', gap:1 }}>
          <Typography variant="h6" sx={{ fontSize: 16, whiteSpace: 'nowrap' }}>
            Verification Demo
          </Typography>
          <Autocomplete
            size="small"
            options={Object.keys(modesConfig || {})}
            value={mode}
            onChange={(e,val) => onChangeMode && onChangeMode(val || 'C')}
            sx={{ width: 140, '& .MuiOutlinedInput-root': { bgcolor:'transparent', color:'#fff', '& fieldset': { borderColor:'rgba(255,255,255,0.5)' } } }}
            disableClearable
            renderInput={(params) => <TextField {...params} placeholder="mode" />}
          />
        </Box>

        {/* Spacer */}
        <Box sx={{ flex: 1 }} />

        {/* Config Save/Load */}
        <IconButton
          color="inherit"
          onClick={onSaveConfig}
          title="Download config"
          sx={{ p: 0.5 }}
        >
          <SaveAltIcon />
        </IconButton>
        <IconButton
          color="inherit"
          onClick={onLoadConfig}
          title="Load config"
          sx={{ p: 0.5 }}
        >
          <FolderOpenIcon />
        </IconButton>
        <IconButton
          color="inherit"
          onClick={onCopyLink}
          title="Copy shareable link"
          sx={{ p: 0.5 }}
        >
          <LinkIcon />
        </IconButton>

        {/* Login/Logout */}
        {!signedIn ? (
          <Button color="inherit" onClick={onOpenLogin}>
            Login
          </Button>
        ) : (
          <Button color="inherit" onClick={onLogout}>
            Sign out
          </Button>
        )}
      </MuiToolbar>
    </AppBar>
  )
}
