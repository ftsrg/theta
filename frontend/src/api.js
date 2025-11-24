import axios from 'axios';

const API_ROOT = import.meta.env.VITE_API_ROOT || 'https://localhost:5175';

let onAuthRequired = null;
export function setAuthRequiredHandler(cb) { onAuthRequired = cb; }

export const api = axios.create({
  baseURL: API_ROOT,
  timeout: 20000
});

// CSRF token cached client-side
let csrfToken = null;
export function setCsrfToken(tok) { csrfToken = tok; }
export function getCsrfToken() { return csrfToken; }

api.interceptors.request.use((config) => {
  try {
    const token = localStorage.getItem('thetaAuth');
    if (token) {
      config.headers = config.headers || {};
      // Always send Authorization if we have it; backend only enforces on protected routes.
      config.headers.Authorization = token;
      const c = getCsrfToken();
      if (c) config.headers['X-CSRF-TOKEN'] = c;
    }
  } catch (_) {}
  return config;
}, (err) => Promise.reject(err));

api.interceptors.response.use((res) => res, async (err) => {
  const status = err?.response?.status;
  const originalConfig = err?.config;
  if (status === 401) {
    localStorage.removeItem('thetaAuth');
    if (onAuthRequired) onAuthRequired('Unauthorized – please sign in to build versions.');
  }
  // Auto refresh CSRF only for build endpoint when token invalid/missing (403) and not retried yet
  if (status === 403 && originalConfig && /\/api\/theta\/build$/.test(originalConfig.url || '') && !originalConfig._csrfRetry) {
    const msg = err.response?.data?.error || '';
    if (/invalid or missing csrf token/i.test(msg)) {
      const auth = localStorage.getItem('thetaAuth');
      if (auth) {
        try {
          const refresh = await api.post('/api/auth/csrf');
          if (refresh?.data?.token) {
            setCsrfToken(refresh.data.token);
            originalConfig._csrfRetry = true;
            originalConfig.headers = originalConfig.headers || {};
            originalConfig.headers['X-CSRF-TOKEN'] = refresh.data.token;
            return api.request(originalConfig);
          }
        } catch (_) {
          // swallow and fall through to reject original error
        }
      }
    }
  }
  return Promise.reject(err);
});
