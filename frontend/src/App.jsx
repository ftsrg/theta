import React, { useEffect, useState, useRef } from 'react'
import Split from 'react-split'
import Editor from './components/Editor'
import OutputPanel from './components/OutputPanel'
import Toolbar from './components/Toolbar'
import { Dialog, DialogTitle, DialogContent, DialogActions, TextField, Snackbar, Alert, LinearProgress, Box, Button, Typography, useMediaQuery } from '@mui/material'
import { useTheme } from '@mui/material/styles'
import { api, setAuthRequiredHandler, setCsrfToken, getCsrfToken } from './api'

const API_ROOT = import.meta.env.VITE_API_ROOT || 'https://localhost:5175'

export default function App() {
  const theme = useTheme()
  const isNarrow = useMediaQuery('(max-width:1000px)')
  const [examples, setExamples] = useState([])
  const [properties, setProperties] = useState([])
  const [selectedExample, setSelectedExample] = useState('')
  const [selectedProperty, setSelectedProperty] = useState('unreach-call.prp')
  const [isXsts, setIsXsts] = useState(false)
  const [code, setCode] = useState(() => {
    const saved = window.localStorage.getItem('thetaCode')
    return saved || '// select an example or start typing...'
  })
  const [verifyOutput, setVerifyOutput] = useState(null)
  const [thetaVersions, setThetaVersions] = useState([]) // [{name,jars:[]}] retrieved
  const [thetaReleases, setThetaReleases] = useState([]) // [{tag, assets:[{name}]}]
  const [position, setPosition] = useState({ line: 1, column: 1 })
  const [loginOpen, setLoginOpen] = useState(false)
  const [username, setUsername] = useState('')
  const [password, setPassword] = useState('')
  const [authToken, setAuthToken] = useState(() => window.localStorage.getItem('thetaAuth') || '')
  const [authNoticeOpen, setAuthNoticeOpen] = useState(false)
  const [authNoticeMsg, setAuthNoticeMsg] = useState('')

  const [toastOpen, setToastOpen] = useState(false)
  const [toastMsg, setToastMsg] = useState('')
  const [toastSeverity, setToastSeverity] = useState('success')
  const [cliPresets, setCliPresets] = useState([])

  // Retrieval streaming dialog state
  const [retrieveOpen, setRetrieveOpen] = useState(false)
  const [retrieveLines, setRetrieveLines] = useState([])
  const [retrieveLabel, setRetrieveLabel] = useState('')
  const [retrieveActive, setRetrieveActive] = useState(false)
  const [retrievePct, setRetrievePct] = useState(0)
  const [retrieveSpeed, setRetrieveSpeed] = useState(0)
  const [retrieveEta, setRetrieveEta] = useState(0)
  const [verifyRunning, setVerifyRunning] = useState(false)
  const [verifyRunId, setVerifyRunId] = useState('')

  // Save code to localStorage on every change
  useEffect(() => {
    window.localStorage.setItem('thetaCode', code)
  }, [code])

  // Auth handler
  useEffect(() => {
    setAuthRequiredHandler((msg) => {
      if (msg) { setAuthNoticeMsg(msg); setAuthNoticeOpen(true); }
      setAuthToken('')
      setLoginOpen(true)
    })
    api.get('/api/examples').then(r => {
      const exs = r.data || []
      setExamples(exs)
    }).catch(()=>{})
    api.get('/api/properties').then(r => {
      const props = r.data || []
      setProperties(props)
    }).catch(()=>{})
    api.get('/api/configs').then(r => {
      const presets = r.data?.presets || []
      setCliPresets(presets)
    }).catch(()=>{})
    if(signedIn) { 
      api.post('/api/auth/csrf').then((resp) => {    
      if (resp.data?.token) setCsrfToken(resp.data.token)
        refreshThetaVersions()
        refreshThetaReleases()
      })
    } else {
        refreshThetaVersions()
        refreshThetaReleases()
    }
    const iv = setInterval(() => { refreshThetaVersions() }, 30000) // periodic refresh of versions
    return () => clearInterval(iv)
  }, [])

  useEffect(() => { if (selectedExample) api.get(`/api/examples/${selectedExample}`).then(r => setCode(r.data.content || '')) }, [selectedExample])

  const signedIn = !!authToken
  const openLogin = () => setLoginOpen(true)

  const fetchCsrf = async () => {
    try { const resp = await api.post('/api/auth/csrf'); if (resp.data?.token) setCsrfToken(resp.data.token) } catch { setAuthNoticeMsg('Failed to obtain CSRF'); setAuthNoticeOpen(true) }
  }

  const refreshThetaVersions = () => {
    api.get('/api/theta/versions').then(r => setThetaVersions(r.data.versions || [])).catch(()=>{})
  }
  const refreshThetaReleases = () => {
    const headers = {};
    const csrf = getCsrfToken();
    if (csrf) headers['X-CSRF-TOKEN'] = csrf;
    api.get('/api/theta/releases', { headers }).then(r => setThetaReleases(r.data.releases || [])).catch(()=>{})
  }


  const doLogin = async () => {
    const candidate = 'Basic ' + btoa(`${username}:${password}`)
    try {
      const resp = await api.post('/api/auth/validate', {}, { headers: { Authorization: candidate } })
      if (!resp.data?.ok) throw new Error('invalid')
      window.localStorage.setItem('thetaAuth', candidate)
      setAuthToken(candidate)
      setUsername('')
      setPassword('')
      setLoginOpen(false)
      await fetchCsrf()
    } catch {
      setAuthNoticeMsg('Login failed: invalid credentials')
      setAuthNoticeOpen(true)
    }
  }
  const doLogout = () => { window.localStorage.removeItem('thetaAuth'); setAuthToken('') }

  const onSelectExample = (path) => setSelectedExample(path)

  // Verification (streaming)
  const runVerification = async ({ binaryName, args, thetaVersion, jarFile }) => {
    setVerifyOutput({ stdout: '', stderr: '' })
    setVerifyRunning(true)
    setVerifyRunId('')
    try {
      const resp = await fetch(`${API_ROOT}/api/verify/stream`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ code, binaryName, args, thetaVersion, jarFile })
      })
      if (!resp.ok || !resp.body) throw new Error(`HTTP ${resp.status}`)
      const reader = resp.body.getReader(); const decoder = new TextDecoder(); let buf=''; let sawResult=false
      while(true){ const {done,value}=await reader.read(); if(done) break; buf+=decoder.decode(value,{stream:true}); let idx; while((idx=buf.indexOf('\n'))>=0){ const line=buf.slice(0,idx).replace(/\r$/,''); buf=buf.slice(idx+1); if(!line) continue; if(line.startsWith('RUN: ')){ setVerifyRunId(line.slice(5).trim()) } else if(line.startsWith('OUT: ')){ const msg=line.slice(5); setVerifyOutput(prev=>({...prev, stdout:(prev.stdout?prev.stdout+'\n':'')+msg})) } else if(line.startsWith('ERR: ')){ const msg=line.slice(5); setVerifyOutput(prev=>({...prev, stderr:(prev.stderr?prev.stderr+'\n':'')+msg})) } else if(line.startsWith('RESULT: ')){ try{ const obj=JSON.parse(line.slice(8)); sawResult=true; setVerifyOutput(prev=>({ ...obj, stdout: prev.stdout||'', stderr: prev.stderr||'' })) ; setToastMsg('Verification finished'); setToastSeverity(obj.code===0?'success':'warning'); setToastOpen(true);}catch(e){ /* ignore parse error */ } } }
      }
      if(!sawResult){ setToastMsg('Verification finished (no result)'); setToastSeverity('warning'); setToastOpen(true) }
    } catch (err) {
      setVerifyOutput(prev=>({ ...(prev||{}), code: -1, error: String(err) }))
      setToastMsg('Verification failed')
      setToastSeverity('error')
      setToastOpen(true)
    } finally {
      setVerifyRunning(false)
      setVerifyRunId('')
    }
  }

  const cancelVerification = async () => {
    if (!verifyRunId) return
    try { await api.post('/api/verify/cancel', { runId: verifyRunId }) } catch {}
  }

  // Retrieval streaming (simplified parser matching server.js current format)
  const retrieveStartRef = useRef(0)
  const [retrieveTotalSize, setRetrieveTotalSize] = useState(0)
  const appendRetrieveLine = (line) => {
    // Size header line
    if (/^Downloading .*\((\d+) bytes\)$/.test(line)) {
      const m = line.match(/\((\d+) bytes\)$/)
      if (m) setRetrieveTotalSize(parseInt(m[1],10))
    }
    if (/^DONE:/.test(line)) {
      setRetrievePct(100)
      setRetrieveEta(0)
    }
    // Progress line primary format: PROGRESS <pct>% <received>/<size> <speed>KB/s ETA:<eta>s
    if (/^PROGRESS: /.test(line)) {
      const m = line.match(/^PROGRESS: (\d+)\/(\d+)$/)
      if (m) {
        const received = parseInt(m[1],10)
        const retrieveTotalSize = parseInt(m[2],10)
        const pct = Math.floor(received / retrieveTotalSize * 100)
        const elapsedMs = Date.now() - retrieveStartRef.current
        const speed = elapsedMs > 0 ? (received / 1024) / (elapsedMs / 1000) : 0
        const remain = retrieveTotalSize - received
        const etaSec = speed > 0 ? Math.round(remain / 1024 / speed) : 0
        setRetrievePct(pct)
        setRetrieveSpeed(Math.round(speed))
        setRetrieveEta(etaSec)
      }
    } else {
      setRetrieveLines(ls => [...ls, line])
    }
  }
  const startStreamingRetrieve = async (version, jar, onSuccess) => {
    if (!version || !jar) return
    setRetrieveLabel(`${version} / ${jar}`)
    setRetrieveLines([])
    setRetrieveActive(true)
    setRetrievePct(0); setRetrieveSpeed(0); setRetrieveEta(0)
    setRetrieveTotalSize(0)
    retrieveStartRef.current = Date.now()
    setRetrieveOpen(true)
    const body = JSON.stringify({ version, assetName: jar })
    const attempt = async () => {
      let resp = await fetch(`${API_ROOT}/api/theta/retrieve/stream`, { method: 'POST', headers: { 'Content-Type': 'application/json', 'Authorization': authToken, 'X-CSRF-TOKEN': getCsrfToken() || '' }, body })
      if (resp.status === 403) { try { await fetchCsrf(); } catch {}; if (getCsrfToken()) resp = await fetch(`${API_ROOT}/api/theta/retrieve/stream`, { method: 'POST', headers: { 'Content-Type': 'application/json', 'Authorization': authToken, 'X-CSRF-TOKEN': getCsrfToken() || '' }, body }) }
      return resp
    }
    try {
      const resp = await attempt();
      if (!resp.ok) { appendRetrieveLine(`ERROR: HTTP ${resp.status}`); setRetrieveActive(false); return; }
      const reader = resp.body.getReader(); const decoder = new TextDecoder(); let buf='';
      while(true){ const {done,value}=await reader.read(); if(done)break; buf+=decoder.decode(value,{stream:true}); let idx; while((idx=buf.indexOf('\n'))>=0){ const line=buf.slice(0,idx).replace(/\r$/,''); buf=buf.slice(idx+1); if(line) appendRetrieveLine(line); if(/^DONE:/.test(line)){ setRetrieveActive(false); onSuccess && onSuccess(); } if(/^ERROR:/.test(line)){ setRetrieveActive(false); } } }
    } catch(e){ appendRetrieveLine(`ERROR: ${e.message}`); setRetrieveActive(false); }
  }
  const cancelRetrieve = async () => { if (!retrieveActive) return; const version = retrieveLabel.split(' / ')[0]; try { await api.post('/api/theta/retrieve/cancel', { version }); } catch {} }
  const closeRetrieve = () => { if (!retrieveActive) setRetrieveOpen(false) }

  const requestLoginForVersion = (version, jar) => { openLogin() }

  const closeAuthNotice = (_, reason) => { if (reason === 'clickaway') return; setAuthNoticeOpen(false) }

  const handleJarContextChange = ({ isXsts: nextIsXsts }) => {
    setIsXsts(!!nextIsXsts)
    if (nextIsXsts) {
      if (selectedProperty && selectedProperty.endsWith('.prp')) {
        setSelectedProperty('')
      }
    } else {
      if (!selectedProperty || !selectedProperty.endsWith('.prp')) {
        const fallback = properties.includes('unreach-call.prp') ? 'unreach-call.prp' : (properties[0] || 'unreach-call.prp')
        setSelectedProperty(fallback)
      }
    }
  }

  return (
    <Box sx={{ height: '100vh', display: 'flex', flexDirection: 'column' }}>
      <Toolbar
        signedIn={signedIn}
        onOpenLogin={openLogin}
        onLogout={doLogout}
      />

      <Box sx={{ flex: 1, display: 'flex', minHeight: 0 }}>
        {isNarrow ? (
          // Stacked layout for narrow screens
          <Box sx={{ display: 'flex', flexDirection: 'column', width: '100%', height: '100%' }}>
            <Box sx={{ height: '50%', minHeight: 0, display: 'flex', flexDirection: 'column', borderBottom: '1px solid #2a3138' }}>
              <Editor
                code={code}
                onChange={setCode}
                onPositionChange={setPosition}
                examples={examples}
                properties={properties}
                selectedProperty={selectedProperty}
                isXsts={isXsts}
                onSelectExample={onSelectExample}
                onSelectProperty={setSelectedProperty}
              />
            </Box>
            <Box sx={{ height: '50%', minHeight: 0, display: 'flex', flexDirection: 'column' }}>
              <OutputPanel
                result={verifyOutput}
                versions={thetaVersions}
                releases={thetaReleases}
                signedIn={signedIn}
                verifyRunning={verifyRunning}
                selectedProperty={selectedProperty}
                onJarContextChange={handleJarContextChange}
                onRun={runVerification}
                onRefreshVersions={refreshThetaVersions}
                onRequestLogin={(version) => requestLoginForVersion(version, null)}
                onStreamRetrieve={(ver, jar, cb) => signedIn ? startStreamingRetrieve(ver, jar, cb) : requestLoginForVersion(ver, jar)}
                onCancelVerification={cancelVerification}
                presets={cliPresets}
              />
            </Box>
          </Box>
        ) : (
          // Split layout for wide screens
          <Split sizes={[50,50]} minSize={200} gutterSize={8} gutterAlign="center" className="split" style={{ display:'flex', width:'100%', height:'100%' }}>
            <div style={{ width:'100%', height:'100%', display:'flex', flexDirection:'column' }}>
              <Editor
                code={code}
                onChange={setCode}
                onPositionChange={setPosition}
                examples={examples}
                properties={properties}
                selectedProperty={selectedProperty}
                isXsts={isXsts}
                onSelectExample={onSelectExample}
                onSelectProperty={setSelectedProperty}
              />
            </div>
            <div style={{ width:'100%', height:'100%', display:'flex', flexDirection:'column' }}>
              <OutputPanel
                result={verifyOutput}
                versions={thetaVersions}
                releases={thetaReleases}
                signedIn={signedIn}
                verifyRunning={verifyRunning}
                selectedProperty={selectedProperty}
                onJarContextChange={handleJarContextChange}
                onRun={runVerification}
                onRefreshVersions={refreshThetaVersions}
                onRequestLogin={(version) => requestLoginForVersion(version, null)}
                onStreamRetrieve={(ver, jar, cb) => signedIn ? startStreamingRetrieve(ver, jar, cb) : requestLoginForVersion(ver, jar)}
                onCancelVerification={cancelVerification}
                presets={cliPresets}
              />
            </div>
          </Split>
        )}
      </Box>

      <Box component="footer" className="footer" sx={{ display:'flex', justifyContent:'space-between', alignItems:'center' }}>
        <Typography variant="caption">Ln {position.line}, Col {position.column}</Typography>
        <Typography variant="caption">Theta licensed under Apache-2.0. SMT solver may have different licensing. Check before using.</Typography>
      </Box>

      <Dialog open={loginOpen} onClose={() => setLoginOpen(false)} maxWidth="xs" fullWidth>
        <DialogTitle>Sign in</DialogTitle>
        <DialogContent>
          <Box sx={{ display:'flex', flexDirection:'column', gap:2, mt:1 }}>
            <TextField label="Username" size="small" value={username} onChange={e=>setUsername(e.target.value)} autoFocus />
            <TextField label="Password" type="password" size="small" value={password} onChange={e=>setPassword(e.target.value)} />
            <Typography variant="caption" sx={{ opacity:0.7 }}>Credentials stored locally; used only for retrieval.</Typography>
          </Box>
        </DialogContent>
        <DialogActions>
          <Button onClick={() => setLoginOpen(false)}>Cancel</Button>
          <Button variant="contained" onClick={doLogin} disabled={!username || !password}>Sign in</Button>
        </DialogActions>
      </Dialog>

      <Snackbar open={authNoticeOpen} autoHideDuration={4000} onClose={closeAuthNotice} anchorOrigin={{ vertical:'bottom', horizontal:'center' }}>
        <Alert onClose={closeAuthNotice} severity="warning" variant="filled" sx={{ width:'100%' }}>{authNoticeMsg || 'Authorization required.'}</Alert>
      </Snackbar>
      <Snackbar open={toastOpen} autoHideDuration={4000} onClose={()=>setToastOpen(false)} anchorOrigin={{ vertical:'bottom', horizontal:'right' }}>
        <Alert onClose={()=>setToastOpen(false)} severity={toastSeverity} variant="filled" sx={{ width:'100%' }}>{toastMsg}</Alert>
      </Snackbar>

      <Dialog open={retrieveOpen} onClose={closeRetrieve} fullWidth maxWidth="md">
        <DialogTitle>Retrieval: {retrieveLabel}</DialogTitle>
        <DialogContent dividers>
          <Box sx={{ mb:2 }}>
            <LinearProgress variant="determinate" value={retrievePct} />
            <Typography variant="caption" sx={{ display:'block', mt:0.5 }}>
              {retrieveActive ? `${retrievePct}% • ${retrieveSpeed} KB/s • ETA ${retrieveEta}s` : (retrievePct===100 ? 'Completed' : 'Idle')}
            </Typography>
          </Box>
          <Box sx={{ fontFamily:'monospace', fontSize:12, maxHeight:400, overflow:'auto', whiteSpace:'pre-wrap' }}>
            {retrieveLines.join('\n')}
          </Box>
        </DialogContent>
        <DialogActions>
          {retrieveActive && <Button color="error" onClick={cancelRetrieve}>Cancel</Button>}
          <Button onClick={closeRetrieve} disabled={retrieveActive}>Close</Button>
        </DialogActions>
      </Dialog>
    </Box>
  )
}
