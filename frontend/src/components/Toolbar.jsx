import React from 'react'
import { AppBar, Toolbar as MuiToolbar, Button, Box, Typography, IconButton } from '@mui/material'
import GitHubIcon from '@mui/icons-material/GitHub'

export default function Toolbar({ signedIn = false, onOpenLogin, onLogout }) {
  return (
    <AppBar position="static" className="app-toolbar" elevation={0}>
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

        {/* Title */}
        <Typography variant="h6" sx={{ fontSize: 16, whiteSpace: 'nowrap' }}>
          Verification Demo
        </Typography>

        {/* Spacer */}
        <Box sx={{ flex: 1 }} />

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
