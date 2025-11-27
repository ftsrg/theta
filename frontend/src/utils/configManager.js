/**
 * Centralized configuration management for Theta WebUI
 * Handles per-mode storage, serialization, and restoration of user settings
 */

const CONFIG_KEY_PREFIX = 'thetaConfig_'
const MODE_KEY = 'thetaMode'
const AUTH_KEY = 'thetaAuth'

/**
 * Default configuration structure for a mode
 */
const getDefaultConfig = (mode) => ({
  code: '// select an example or start typing...',
  selectedProperty: mode === 'XSTS' ? '' : 'unreach-call.prp',
  selectedExample: '',
  selectedRelease: '',
  selectedPreset: '',
  args: mode === 'XSTS' 
    ? 'CEGAR --model %in --inline-property %prop'
    : '--input %in --property %prop --backend PORTFOLIO'
})

/**
 * Save configuration for a specific mode
 */
export function saveConfig(mode, config) {
  if (!mode) return
  
  const key = CONFIG_KEY_PREFIX + mode
  const configToSave = {
    ...getDefaultConfig(mode),
    ...config,
    version: '1.0',
    timestamp: new Date().toISOString()
  }
  
  try {
    localStorage.setItem(key, JSON.stringify(configToSave))
  } catch (err) {
    console.error('Failed to save config:', err)
  }
}

/**
 * Load configuration for a specific mode
 */
export function loadConfig(mode) {
  if (!mode) return getDefaultConfig(mode)
  
  const key = CONFIG_KEY_PREFIX + mode
  try {
    const saved = localStorage.getItem(key)
    if (saved) {
      const parsed = JSON.parse(saved)
      return { ...getDefaultConfig(mode), ...parsed }
    }
  } catch (err) {
    console.error('Failed to load config:', err)
  }
  
  return getDefaultConfig(mode)
}

/**
 * Clear configuration for a specific mode
 */
export function clearConfig(mode) {
  if (!mode) return
  const key = CONFIG_KEY_PREFIX + mode
  try {
    localStorage.removeItem(key)
  } catch (err) {
    console.error('Failed to clear config:', err)
  }
}

/**
 * Get current mode from localStorage
 */
export function getCurrentMode() {
  try {
    return localStorage.getItem(MODE_KEY) || 'C'
  } catch {
    return 'C'
  }
}

/**
 * Set current mode in localStorage
 */
export function setCurrentMode(mode) {
  if (!mode) return
  try {
    localStorage.setItem(MODE_KEY, mode)
  } catch (err) {
    console.error('Failed to set mode:', err)
  }
}

/**
 * Export configuration as JSON (for download)
 */
export function exportConfig(mode, config) {
  const exportData = {
    mode,
    config: {
      ...config,
      version: '1.0',
      exportedAt: new Date().toISOString()
    }
  }
  
  return JSON.stringify(exportData, null, 2)
}

/**
 * Import configuration from JSON
 */
export function importConfig(jsonString) {
  try {
    const data = JSON.parse(jsonString)
    if (!data.mode || !data.config) {
      throw new Error('Invalid config format')
    }
    return {
      mode: data.mode,
      config: data.config
    }
  } catch (err) {
    console.error('Failed to import config:', err)
    throw err
  }
}

/**
 * Parse URL parameters for mode and config override
 */
export function parseUrlConfig() {
  if (typeof window === 'undefined') return null
  
  try {
    const params = new URLSearchParams(window.location.search)
    const mode = params.get('mode')
    const configParam = params.get('config')
    
    if (mode && configParam) {
      // Decode base64 JSON
      const decoded = atob(configParam)
      const config = JSON.parse(decoded)
      return { mode, config }
    }
  } catch (err) {
    console.error('Failed to parse URL config:', err)
  }
  
  return null
}

/**
 * Generate URL with mode and config parameters
 */
export function generateConfigUrl(mode, config) {
  if (typeof window === 'undefined') return ''
  
  try {
    const baseUrl = window.location.origin + window.location.pathname
    const configJson = JSON.stringify(config)
    const encoded = btoa(configJson)
    return `${baseUrl}?mode=${encodeURIComponent(mode)}&config=${encodeURIComponent(encoded)}`
  } catch (err) {
    console.error('Failed to generate config URL:', err)
    return ''
  }
}

/**
 * Auth token management (separate from mode configs)
 */
export function getAuthToken() {
  try {
    return localStorage.getItem(AUTH_KEY) || ''
  } catch {
    return ''
  }
}

export function setAuthToken(token) {
  try {
    if (token) {
      localStorage.setItem(AUTH_KEY, token)
    } else {
      localStorage.removeItem(AUTH_KEY)
    }
  } catch (err) {
    console.error('Failed to set auth token:', err)
  }
}

export function clearAuthToken() {
  try {
    localStorage.removeItem(AUTH_KEY)
  } catch (err) {
    console.error('Failed to clear auth token:', err)
  }
}

/**
 * Update a single field in the current mode's config
 */
export function updateConfigField(mode, field, value) {
  const current = loadConfig(mode)
  current[field] = value
  saveConfig(mode, current)
}

/**
 * Migrate old localStorage format to new centralized format
 */
export function migrateOldConfig() {
  const modes = ['C', 'CHC', 'XSTS']
  
  modes.forEach(mode => {
    // Check if already migrated
    const newKey = CONFIG_KEY_PREFIX + mode
    if (localStorage.getItem(newKey)) return
    
    // Migrate old keys
    const config = getDefaultConfig(mode)
    
    const oldCodeKey = `thetaCode_${mode}`
    const oldPropKey = `thetaProperty_${mode}`
    
    const oldCode = localStorage.getItem(oldCodeKey)
    const oldProp = localStorage.getItem(oldPropKey)
    
    if (oldCode) config.code = oldCode
    if (oldProp) config.selectedProperty = oldProp
    
    // Save to new format
    saveConfig(mode, config)
    
    // Clean up old keys
    localStorage.removeItem(oldCodeKey)
    localStorage.removeItem(oldPropKey)
  })
  
  // Migrate global settings
  const oldRelease = localStorage.getItem('theta.selectedRelease')
  const oldPreset = localStorage.getItem('theta.selectedPresetName')
  
  if (oldRelease || oldPreset) {
    modes.forEach(mode => {
      const config = loadConfig(mode)
      if (oldRelease) config.selectedRelease = oldRelease
      if (oldPreset) config.selectedPreset = oldPreset
      saveConfig(mode, config)
    })
    
    localStorage.removeItem('theta.selectedRelease')
    localStorage.removeItem('theta.selectedPresetName')
  }
}
