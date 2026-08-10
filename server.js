const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { fork } = require('child_process');
const pdfParse = require('pdf-parse');

const HOST = process.env.HOST || '127.0.0.1';
const PORT = Number(process.env.PORT || 8787);
const ROOT = __dirname;
const PUBLIC_ROOT = path.join(ROOT, 'public');
const CONFIG_FILE = process.env.AKFIX_CONFIG_FILE || path.join(ROOT, 'config.local.json');
const DASHBOARD_SNAPSHOT_FILE = process.env.AKFIX_SNAPSHOT_FILE || path.join(ROOT, 'dashboard.snapshot.json');
const CARRIER_ARCHIVE_FILE = process.env.AKFIX_CARRIER_ARCHIVE_FILE || path.join(ROOT, 'carrier.archive.json');
const INVOICE_QUANTITY_CACHE_FILE = process.env.AKFIX_INVOICE_CACHE_FILE || path.join(ROOT, 'invoice.quantity-cache.json');
const BASIC_USER = process.env.AKFIX_BASIC_USER || '';
const BASIC_PASSWORD = process.env.AKFIX_BASIC_PASSWORD || '';
const authSessions = new Map();
const AUTH_SESSION_TTL = 12 * 60 * 60 * 1000;
const baikalCache = new Map();
const baikalInflight = new Map();
const baikalDetailCache = new Map();
const BITRIX_PHOTO_FIELDS = [
  'ufCrm19_1752654002268',
  'ufCrm19_1752654317973',
  'ufCrm19_1761641310794',
  'ufCrm19_1751013626434',
];
const BITRIX_INVOICE_FIELD = 'ufCrm19_1751013626434';
let megatransCache = { expiresAt: 0, data: null };
let dellinCache = { expiresAt: 0, data: null };
let bitrixCache = { expiresAt: 0, data: null };
const bitrixPhotoItemCache = new Map();
let googleLogisticsCache = { expiresAt: 0, data: null };
let cdekTokenCache = { expiresAt: 0, token: '' };
let invoiceQuantityCache = (() => { try { return JSON.parse(fs.readFileSync(INVOICE_QUANTITY_CACHE_FILE, 'utf8')); } catch { return {}; } })();
let cdekSamplesCache = { expiresAt: 0, data: null };
const GOOGLE_LOGISTICS_CSV = process.env.GOOGLE_LOGISTICS_CSV || 'https://docs.google.com/spreadsheets/d/18H4xoO7DFMsIml68G-Ama_fxjc3EW8-tbcKBCtAuuC4/export?format=csv&gid=0';

function json(res, status, data) {
  res.writeHead(status, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
  });
  res.end(JSON.stringify(data));
}

function safeEqual(left, right) {
  const a = Buffer.from(String(left));
  const b = Buffer.from(String(right));
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}

function parseCookies(req) {
  return Object.fromEntries(String(req.headers.cookie || '').split(';').map(part => part.trim()).filter(Boolean).map(part => {
    const index = part.indexOf('=');
    return index < 0 ? [part, ''] : [part.slice(0, index), decodeURIComponent(part.slice(index + 1))];
  }));
}

function configuredAuthUsers() {
  try { return Array.isArray(loadConfig().authUsers) ? loadConfig().authUsers : []; }
  catch (_) { return []; }
}

function sessionForRequest(req) {
  const token = parseCookies(req).akfix_session;
  const session = token ? authSessions.get(token) : null;
  if (!session) return null;
  if (session.expiresAt <= Date.now()) { authSessions.delete(token); return null; }
  return session;
}

function authorizeRequest(req, res) {
  const users = configuredAuthUsers();
  if (users.length) {
    const session = sessionForRequest(req);
    if (session) { req.auth = session; return true; }
    json(res, 401, { error: 'Требуется авторизация' });
    return false;
  }
  if (!BASIC_USER || !BASIC_PASSWORD) return true;
  const header = String(req.headers.authorization || '');
  if (header.startsWith('Basic ')) {
    try {
      const decoded = Buffer.from(header.slice(6), 'base64').toString('utf8');
      const separator = decoded.indexOf(':');
      const user = separator >= 0 ? decoded.slice(0, separator) : '';
      const password = separator >= 0 ? decoded.slice(separator + 1) : '';
      if (safeEqual(user, BASIC_USER) && safeEqual(password, BASIC_PASSWORD)) return true;
    } catch (_) {}
  }
  res.writeHead(401, {
    'WWW-Authenticate': 'Basic realm="Akfix Logistics", charset="UTF-8"',
    'Content-Type': 'text/plain; charset=utf-8',
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
  });
  res.end('Требуется авторизация');
  return false;
}

function verifyPassword(password, user) {
  if (!user?.salt || !user?.passwordHash) return false;
  const actual = crypto.scryptSync(String(password), user.salt, 64).toString('hex');
  return safeEqual(actual, user.passwordHash);
}

function sanitizeWarehouseDashboardPayload(value) {
  if (Array.isArray(value)) return value.map(sanitizeWarehouseDashboardPayload);
  if (!value || typeof value !== 'object') return value;
  return Object.fromEntries(Object.entries(value)
    .filter(([key]) => key !== 'urlMachine' && key !== 'url')
    .map(([key, item]) => [key, sanitizeWarehouseDashboardPayload(item)]));
}

function loadConfig() {
  return JSON.parse(fs.readFileSync(CONFIG_FILE, 'utf8'));
}

function saveConfig(next) {
  const current = fs.existsSync(CONFIG_FILE) ? JSON.parse(fs.readFileSync(CONFIG_FILE, 'utf8')) : {};
  fs.writeFileSync(CONFIG_FILE, `${JSON.stringify({ ...current, ...next }, null, 2)}\n`, { encoding: 'utf8', mode: 0o600 });
}

function writeDashboardSnapshot(snapshot) {
  const normalized={savedAt:new Date().toISOString(),orders:Array.isArray(snapshot.orders)?snapshot.orders:[],ourDeliveries:Array.isArray(snapshot.ourDeliveries)?snapshot.ourDeliveries:[],selfPickups:Array.isArray(snapshot.selfPickups)?snapshot.selfPickups:[],sheetLogisticsRows:Array.isArray(snapshot.sheetLogisticsRows)?snapshot.sheetLogisticsRows:[],unmatchedMatchOrders:Array.isArray(snapshot.unmatchedMatchOrders)?snapshot.unmatchedMatchOrders:[],cdekShipments:Array.isArray(snapshot.cdekShipments)?snapshot.cdekShipments:[]};
  const temporary=`${DASHBOARD_SNAPSHOT_FILE}.tmp`;
  fs.writeFileSync(temporary,`${JSON.stringify(normalized)}\n`,{encoding:'utf8',mode:0o600});
  fs.renameSync(temporary,DASHBOARD_SNAPSHOT_FILE);
  return normalized;
}

function writeJsonAtomic(file, value) {
  const temporary = `${file}.tmp`;
  fs.writeFileSync(temporary, `${JSON.stringify(value)}\n`, { encoding: 'utf8', mode: 0o600 });
  fs.renameSync(temporary, file);
}

function normalizeMatchText(value) {
  return String(value || '').toLowerCase()
    .replace(/общество\s+с\s+ограниченной\s+ответственностью/gi, ' ')
    .replace(/индивидуальн(?:ый|ого)\s+предпринимател(?:ь|я)/gi, ' ')
    .replace(/(^|[^а-яёa-z0-9])(ооо|ип|ао|пао|зао)(?=$|[^а-яёa-z0-9])/gi, ' ')
    .replace(/[«»"'()]/g, ' ').replace(/[^a-zа-яё0-9]+/gi, ' ').replace(/\s+/g, ' ').trim();
}

function normalizeCarrierKey(value) {
  return normalizeMatchText(value)
    .replace(/^(?:тк|транспортная компания)\s+/i, '')
    .replace(/\b(?:тк|транспортная компания)\b/gi, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

function personInitialsMatch(left, right) {
  const a = normalizeMatchText(left).split(' ').filter(Boolean);
  const b = normalizeMatchText(right).split(' ').filter(Boolean);
  if (a.length < 2 || b.length < 2 || a[0] !== b[0]) return false;
  const initials = tokens => tokens.slice(1).map(token => token[0]).filter(Boolean);
  const ai = initials(a);
  const bi = initials(b);
  const short = ai.length <= bi.length ? ai : bi;
  const long = ai.length <= bi.length ? bi : ai;
  return short.length > 0 && short.every((letter, index) => letter === long[index]);
}

function companyTokensMatch(left, right) {
  const tokens = value => [...new Set(normalizeMatchText(value).split(' ').filter(token => token.length > 1))].sort();
  const a = tokens(left);
  const b = tokens(right);
  if (a.length < 2 || b.length < 2) return false;
  return a.length === b.length && a.every((token, index) => token === b[index]);
}

function counterpartyIdentity(value, config = loadConfig()) {
  const normalized = normalizeMatchText(value);
  const digits = String(value || '').replace(/\D/g, '');
  if (!normalized && digits.length < 10) return '';
  for (const item of config.counterparties || []) {
    const variants = [item.name, ...(item.aliases || []), ...(item.contacts || [])];
    if (variants.some(candidate => normalizeMatchText(candidate) === normalized)) return `counterparty:${item.id}`;
    if (digits.length >= 10 && [item.inn, ...(item.phones || [])].some(candidate => String(candidate || '').replace(/\D/g, '') === digits)) return `counterparty:${item.id}`;
  }
  return normalized;
}

function linkedCounterpartyMatch(left, right, config = loadConfig()) {
  const a = counterpartyIdentity(left, config);
  const b = counterpartyIdentity(right, config);
  return Boolean(a && b && a.startsWith('counterparty:') && a === b);
}

function resolveCarrierAlias(value, config = loadConfig()) {
  const text = String(value || '').trim();
  const aliases = config.carrierAliases || {};
  const normalized = normalizeMatchText(text);
  const carrierKey = normalizeCarrierKey(text);
  const similarKey = carrierKey && Object.keys(aliases).find(key => normalizeCarrierKey(key) === carrierKey);
  const alias = aliases[normalized] || (similarKey ? aliases[similarKey] : '');
  return String(alias || text).trim();
}

function canonicalCompanyDisplay(value) {
  const text = String(value || '').trim();
  const normalized = normalizeMatchText(text).replace(/\s+/g, '');
  return normalized === 'акфиксрус' ? 'ООО «АКФИКС-РУС»' : text;
}

function matchDate(value) {
  const text = String(value || '').trim();
  const ru = text.match(/^(\d{2})\.(\d{2})\.(\d{4})/);
  const date = ru ? new Date(Number(ru[3]), Number(ru[2]) - 1, Number(ru[1])) : new Date(text);
  return Number.isNaN(date.getTime()) ? null : date;
}

function cleanMatchCity(value) {
  const original=String(value||'').replace(/\s+/g,' ').trim();
  if(!original) return '';
  const withoutPostal=original.replace(/(^|[\s,;])\d{6}(?=$|[\s,;])/g,' ');
  const cityMarker=[...withoutPostal.matchAll(/(?:^|[\s,])г\.?\s+/gi)].pop();
  let city=cityMarker ? withoutPostal.slice((cityMarker.index||0)+cityMarker[0].length) : withoutPostal;
  city=city.replace(/^.*?до\s+терминала(?:\s+тк)?[\s,:;—-]*/i,' ')
    .replace(/\([^)]*\)/g,' ').split(/[,(;]/)[0];
  const normalized=normalizeMatchText(city);
  return /^\d{5,6}$/.test(normalized) ? '' : normalized;
}

function mapBaikalArchive(raw) {
  const rows = [];
  for (const order of raw.orderList || []) {
    const details = order.detail?.cargoList || [];
    for (const [index, cargo] of (order.cargoList || []).entries()) {
      const detail = details.find(item => item.guid === cargo.guid || item.number === cargo.number) || {};
      const consignee = detail.consignee || cargo.consignee || {};
      const consignor = detail.consignor || cargo.consignor || {};
      rows.push({
        id: `baikal-${order.number || order.guid}-${cargo.guid || index}`, source: 'baikal', tk: 'Байкал Сервис',
        client: canonicalCompanyDisplay(consignee.name), sender: canonicalCompanyDisplay(consignor.name), clientInn: consignee.inn || '',
        shipmentDate: order.detail?.date || order.date || '', deliveryDate: detail.dateIssued || detail.dateArrivalPlane || '',
        deliveryDateType: detail.dateIssued ? 'Фактическая' : (detail.dateArrivalPlane ? 'Плановая' : ''),
        city: cargo.destination?.name || detail.destination?.name || '', deliveryStatus: cargo.status?.name || detail.status?.name || '',
        tkStatus: cargo.status?.name || detail.status?.name || '', expeditorNumber: order.number || order.detail?.number || '',
        track: cargo.number || detail.number || order.trackingnumber || '', cargoTracking: detail.trackingnumber || order.trackingnumber || '',
        cargoGuid: detail.guid || cargo.guid || '', deliveryCost: Number(detail.total?.sum || cargo.sum || ((order.cargoList || []).length === 1 ? order.total : 0) || 0),
        weight: Number(detail.cargo?.weight ?? cargo.weightcargo ?? 0), volume: Number(detail.cargo?.volume ?? cargo.cubaturecargo ?? 0),
        terminalName: detail.destination?.terminal?.name || cargo.destination?.terminal?.name || '',
        addr: detail.destination?.terminal?.address || cargo.destination?.terminal?.address || '', carrierConnected: true
      });
    }
  }
  return rows;
}

function carrierArchiveKey(row) {
  return [row.source, row.expeditorNumber, row.track, row.id].map(value => String(value || '').trim().toLowerCase()).join('|');
}

async function refreshCarrierArchive(full = false) {
  const previous = fs.existsSync(CARRIER_ARCHIVE_FILE) ? JSON.parse(fs.readFileSync(CARRIER_ARCHIVE_FILE, 'utf8')) : { rows: [] };
  const map = new Map((previous.rows || []).map(row => [carrierArchiveKey(row), row]));
  const sourceResults = [];
  const collect = async (source, loader) => {
    try {
      const rows = await loader();
      rows.forEach(row => map.set(carrierArchiveKey(row), { ...map.get(carrierArchiveKey(row)), ...row, carrierConnected: true }));
      sourceResults.push(`${source}: ${rows.length}`);
    } catch (error) { console.error(`[archive] ${source}: ${error.message}`); }
  };
  await collect('Мегатранс', async () => (await fetchMegatransOrders(full)).orders || []);
  await collect('Деловые Линии', async () => (await fetchDellinOrders(full, full ? 'all' : 90)).orders || []);
  await collect('Байкал Сервис', async () => mapBaikalArchive(await fetchBaikalOrders(full ? 'all' : 90)));
  const archive = { savedAt: new Date().toISOString(), full: Boolean(previous.full || full), rows: [...map.values()] };
  writeJsonAtomic(CARRIER_ARCHIVE_FILE, archive);
  console.log(`[archive] Сохранено ${archive.rows.length}; ${sourceResults.join('; ')}`);
  return archive;
}

function consolidateCarrierShipments(carrierRows) {
  // The Baikal API can return several cargo records for one forwarding note.
  // Treat them as one shipment; otherwise two equal-scored cargo rows make a
  // perfectly valid Bitrix match look ambiguous and it is rejected.
  const shipmentMap = new Map();
  carrierRows.forEach((row, index) => {
    const expeditor = String(row.expeditorNumber || '').replace(/\s+/g, '').toLowerCase();
    const key = expeditor
      ? `${normalizeMatchText(row.tk)}|${expeditor}`
      : `${row.source || ''}|${row.id || row.track || index}`;
    const old = shipmentMap.get(key);
    if (!old) { shipmentMap.set(key, row); return; }
    shipmentMap.set(key, {
      ...old, ...row,
      deliveryCost: Math.max(Number(old.deliveryCost || 0), Number(row.deliveryCost || 0)),
      weight: Math.max(Number(old.weight || 0), Number(row.weight || 0)),
      volume: Math.max(Number(old.volume || 0), Number(row.volume || 0)),
      track: old.track || row.track,
      cargoTracking: old.cargoTracking || row.cargoTracking,
      deliveryStatus: old.deliveryStatus || row.deliveryStatus,
      tkStatus: old.tkStatus || row.tkStatus,
    });
  });
  return [...shipmentMap.values()];
}

function matchOrdersOnServer(bitrixRows, carrierRows) {
  const candidateRows = consolidateCarrierShipments(carrierRows);
  const used = new Set();
  const manual = loadConfig().manualShipmentMatches || {};
  const matchingConfig = loadConfig();
  let matched = 0;
  const carrierFamily=value=>{
    const normalized=normalizeMatchText(value);
    if(/делов/.test(normalized)) return 'dellin';
    if(/байкал/.test(normalized)) return 'baikal';
    if(/мега\s*транс|мегатранс/.test(normalized)) return 'megatrans';
    if(/сд[эе]к|cdek/.test(normalized)) return 'cdek';
    return '';
  };
  let rows = bitrixRows.map(bitrix => {
    const client = normalizeMatchText(bitrix.client);
    const city = cleanMatchCity(bitrix.city || bitrix.addr);
    const date = matchDate(bitrix.shipmentDate || bitrix.date);
    const hint = normalizeMatchText(bitrix.carrierHint || bitrix.tk);
    const hintedFamily=carrierFamily(hint);
    const saved = manual[String(bitrix.schet || '')];
    const ranked = candidateRows.map((carrier, index) => {
      const carrierName = normalizeMatchText(carrier.tk);
      const rowFamily=carrierFamily(carrierName);
      const numbers = [carrier.expeditorNumber, carrier.track, carrier.cargoTracking].map(value => String(value || '').replace(/\s+/g, '').toLowerCase());
      const manualMatch = Boolean(saved && normalizeMatchText(saved.carrier) === carrierName && numbers.includes(String(saved.expeditor || '').replace(/\s+/g, '').toLowerCase()));
      if (!manualMatch && hintedFamily && rowFamily && hintedFamily!==rowFamily) return null;
      if (!manualMatch && !hintedFamily && /байкал|делов|мега/.test(hint) && carrierName && !(hint.includes(carrierName) || carrierName.includes(hint))) return null;
      const carrierClient = normalizeMatchText(carrier.client);
      const exactClient = Boolean(client && carrierClient && client === carrierClient);
      const partialClient = Boolean(client.length >= 6 && carrierClient.length >= 6 && (client.includes(carrierClient) || carrierClient.includes(client)));
      const tokenClient = companyTokensMatch(bitrix.client, carrier.client);
      const linkedClient = linkedCounterpartyMatch(bitrix.client, carrier.client, matchingConfig);
      const initialsClient = personInitialsMatch(bitrix.client, carrier.client);
      const contact = normalizeMatchText(bitrix.contactPerson);
      const contactClient = Boolean(contact && carrierClient && (contact.includes(carrierClient) || carrierClient.includes(contact)));
      const contactInitials = personInitialsMatch(bitrix.contactPerson, carrier.client);
      const linkedContact = linkedCounterpartyMatch(bitrix.contactPerson, carrier.client, matchingConfig);
      const shipping = normalizeMatchText(bitrix.shippingInfo);
      const recipientInShipping = Boolean(carrierClient.length >= 4 && shipping.includes(carrierClient));
      const carrierCity = cleanMatchCity(carrier.city);
      const cityMatch = Boolean(city.length >= 3 && carrierCity.length >= 3 && (city.includes(carrierCity) || carrierCity.includes(city)));
      const carrierDate = matchDate(carrier.shipmentDate || carrier.date);
      const days = date && carrierDate ? Math.abs(date - carrierDate) / 86400000 : null;
      if (!manualMatch && days !== null && days > 7) return null;
      let score = manualMatch ? 1000 : 0;
      if (linkedClient || linkedContact) score += 65;
      else if (exactClient) score += 55;
      else if (partialClient) score += 35;
      else if (tokenClient) score += 55;
      else if (initialsClient) score += 50;
      else if (contactClient || contactInitials || recipientInShipping) score += 50;
      if (cityMatch) score += 15;
      if (days !== null) score += days <= 1 ? 25 : (days <= 3 ? 15 : 5);
      if (hintedFamily && hintedFamily===rowFamily) score += 15;
      else if (hint && carrierName && (hint.includes(carrierName) || carrierName.includes(hint))) score += 10;
      // One carrier shipment is one order by default. Reusing the same
      // expeditor for several accounts is allowed only when the logist links
      // those accounts manually (a confirmed consolidated shipment).
      if (used.has(index) && !manualMatch) return null;
      return { index, score, exactClient, partialClient, tokenClient, linkedClient, linkedContact, initialsClient, contactClient, contactInitials, recipientInShipping, cityMatch, manualMatch };
    }).filter(Boolean).sort((a, b) => b.score - a.score);
    const best = ranked[0];
    const second = ranked[1];
    const uniqueRouteFallback = Boolean(best && best.cityMatch && date && best.score >= 50 && (!second || best.score-second.score >= 15));
    if (!best || (best.score < 80 && !uniqueRouteFallback) || (second && best.score - second.score < 5 && !best.manualMatch)) {
      // A temporary carrier outage must never erase data that was already
      // obtained from its API/LK during an earlier successful refresh.
      const hasSavedCarrierData = bitrix.carrierConnected === true && Boolean(
        bitrix.expeditorNumber || bitrix.track || bitrix.cargoTracking ||
        bitrix.deliveryStatus || bitrix.tkStatus || Number(bitrix.deliveryCost || 0)
      );
      if (hasSavedCarrierData) {
        return { ...bitrix, staleCarrierData: true, bitrixMatched: true };
      }
      return { ...bitrix, deliveryStatus: 'Нет данных API', tkStatus: 'Нет данных API', carrierConnected: false };
    }
    used.add(best.index); matched += 1;
    const carrier = candidateRows[best.index];
    return { ...carrier, ...bitrix, id: bitrix.id || bitrix.bitrixId, source: carrier.source, tk: carrier.tk,
      shipmentDate: carrier.shipmentDate || bitrix.shipmentDate, deliveryDate: carrier.deliveryDate || '',
      deliveryStatus: carrier.deliveryStatus || carrier.tkStatus || '', tkStatus: carrier.tkStatus || carrier.deliveryStatus || '',
      expeditorNumber: carrier.expeditorNumber || '', track: carrier.track || '', cargoTracking: carrier.cargoTracking || '',
      deliveryCost: Number(carrier.deliveryCost || 0), weight: carrier.weight, volume: carrier.volume,
      terminalName: carrier.terminalName || '', addr: carrier.addr || bitrix.addr, carrierConnected: true,
      bitrixMatched: true, matchScore: best.score, matchRule: best.manualMatch ? 'manual-expeditor' : 'server-scoring' };
  });
  // Megatrans does not expose a street or our invoice number for historical
  // shipments. For the two network customers below, distribute only the
  // still-unmatched rows one-to-one inside the same customer and day. The
  // ordering is deterministic, so links do not jump after a refresh. Manual
  // matches and confidently matched shipments always take priority.
  const legacyMegatransClient = value => {
    const normalized = normalizeMatchText(value);
    if (normalized.includes('сити строй')) return 'city-stroy';
    if (normalized.includes('карат терминал')) return 'karat-terminal';
    return '';
  };
  const dayKey = value => {
    const date = matchDate(value);
    if (!date) return '';
    return `${date.getFullYear()}-${String(date.getMonth() + 1).padStart(2, '0')}-${String(date.getDate()).padStart(2, '0')}`;
  };
  const conditionalGroups = new Map();
  rows.forEach((row, rowIndex) => {
    if (row.carrierConnected !== false) return;
    const clientKey = legacyMegatransClient(row.client);
    const dateKey = dayKey(row.shipmentDate || row.date);
    if (!clientKey || !dateKey || carrierFamily(row.carrierHint || row.tk) !== 'megatrans') return;
    const key = `${clientKey}|${dateKey}`;
    if (!conditionalGroups.has(key)) conditionalGroups.set(key, []);
    conditionalGroups.get(key).push(rowIndex);
  });
  let conditionalMatched = 0;
  for (const [groupKey, rowIndexes] of conditionalGroups) {
    const [clientKey, dateKey] = groupKey.split('|');
    const available = candidateRows.map((carrier, index) => ({ carrier, index }))
      .filter(({ carrier, index }) => !used.has(index)
        && carrierFamily(carrier.tk) === 'megatrans'
        && legacyMegatransClient(carrier.client) === clientKey
        && dayKey(carrier.shipmentDate || carrier.date) === dateKey)
      .sort((left, right) => String(left.carrier.expeditorNumber || left.carrier.track || '').localeCompare(String(right.carrier.expeditorNumber || right.carrier.track || ''), 'ru'));
    rowIndexes.sort((left, right) => String(rows[left].schet || '').localeCompare(String(rows[right].schet || ''), 'ru'));
    for (let position = 0; position < Math.min(rowIndexes.length, available.length); position += 1) {
      const rowIndex = rowIndexes[position];
      const { carrier, index } = available[position];
      const bitrix = rows[rowIndex];
      used.add(index);
      rows[rowIndex] = { ...carrier, ...bitrix, id:bitrix.id || bitrix.bitrixId, source:carrier.source, tk:carrier.tk,
        shipmentDate:carrier.shipmentDate || bitrix.shipmentDate, deliveryDate:carrier.deliveryDate || '',
        deliveryStatus:carrier.deliveryStatus || carrier.tkStatus || '', tkStatus:carrier.tkStatus || carrier.deliveryStatus || '',
        expeditorNumber:carrier.expeditorNumber || '', track:carrier.track || '', cargoTracking:carrier.cargoTracking || '',
        deliveryCost:Number(carrier.deliveryCost || 0), weight:carrier.weight, volume:carrier.volume,
        terminalName:carrier.terminalName || '', addr:bitrix.addr || carrier.addr, carrierConnected:true,
        bitrixMatched:true, conditionalMatch:true, matchScore:0, matchRule:'legacy-megatrans-sequential' };
      matched += 1;
      conditionalMatched += 1;
    }
  }
  console.log(`[matching] Сопоставлено ${matched} из ${bitrixRows.length}; условно Мегатранс: ${conditionalMatched}`);
  return rows;
}

function usedSnapshotCarrier(carrier, rows) {
  const key = [carrier.source, carrier.expeditorNumber, carrier.track].map(value => String(value || '').trim().toLowerCase()).join('|');
  return rows.some(row => [row.source, row.expeditorNumber, row.track].map(value => String(value || '').trim().toLowerCase()).join('|') === key);
}

function applyManualMatchesToSavedSnapshot(rows) {
  if (!fs.existsSync(DASHBOARD_SNAPSHOT_FILE) || !fs.existsSync(CARRIER_ARCHIVE_FILE)) return 0;
  try {
    const snapshot = JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE, 'utf8'));
    const archive = JSON.parse(fs.readFileSync(CARRIER_ARCHIVE_FILE, 'utf8'));
    const carrierFamily = value => {
      const normalized = normalizeMatchText(value);
      if (/делов/.test(normalized)) return 'dellin';
      if (/байкал/.test(normalized)) return 'baikal';
      if (/мега\s*транс|мегатранс/.test(normalized)) return 'megatrans';
      return '';
    };
    const byNumber = new Map();
    for (const carrier of consolidateCarrierShipments(archive.rows || [])) {
      const family = carrierFamily(carrier.tk);
      for (const value of [carrier.expeditorNumber, carrier.track, carrier.cargoTracking]) {
        const number = String(value || '').replace(/\s+/g, '').toLowerCase();
        if (family && number) byNumber.set(`${family}|${number}`, carrier);
      }
    }
    const requested = new Map(rows.map(row => [String(row.schet || '').trim().toUpperCase(), row]));
    let resolved = 0;
    snapshot.orders = (snapshot.orders || []).map(order => {
      const manual = requested.get(String(order.schet || '').trim().toUpperCase());
      if (!manual) return order;
      const number = String(manual.expeditor || '').replace(/\s+/g, '').toLowerCase();
      const carrier = byNumber.get(`${carrierFamily(manual.carrier)}|${number}`);
      if (!carrier) return order;
      resolved += 1;
      return {
        ...carrier, ...order, id: order.id || order.bitrixId, source: carrier.source, tk: carrier.tk,
        shipmentDate: carrier.shipmentDate || order.shipmentDate, deliveryDate: carrier.deliveryDate || '',
        deliveryStatus: carrier.deliveryStatus || carrier.tkStatus || '', tkStatus: carrier.tkStatus || carrier.deliveryStatus || '',
        expeditorNumber: carrier.expeditorNumber || '', track: carrier.track || '', cargoTracking: carrier.cargoTracking || '',
        deliveryCost: Number(carrier.deliveryCost || 0), weight: carrier.weight, volume: carrier.volume,
        terminalName: carrier.terminalName || '', addr: carrier.addr || order.addr, carrierConnected: true,
        bitrixMatched: true, matchScore: 1000, matchRule: 'manual-expeditor'
      };
    });
    if (resolved) {
      const resolvedAccounts = new Set(rows.map(row => String(row.schet || '').trim().toUpperCase()));
      snapshot.unmatchedMatchOrders = (snapshot.unmatchedMatchOrders || []).filter(order => !resolvedAccounts.has(String(order.schet || '').trim().toUpperCase()));
      snapshot.savedAt = new Date().toISOString();
      writeJsonAtomic(DASHBOARD_SNAPSHOT_FILE, snapshot);
    }
    return resolved;
  } catch (error) {
    console.error('[matching] Не удалось сразу обновить снимок:', error.message);
    return 0;
  }
}

function learnCounterpartiesFromManualMatches(config, rows) {
  if (!fs.existsSync(DASHBOARD_SNAPSHOT_FILE) || !fs.existsSync(CARRIER_ARCHIVE_FILE)) return { counterparties:[...(config.counterparties || [])], learned:0 };
  try {
    const snapshot = JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE, 'utf8'));
    const archive = JSON.parse(fs.readFileSync(CARRIER_ARCHIVE_FILE, 'utf8'));
    const orders = [...(snapshot.orders || []), ...(snapshot.unmatchedMatchOrders || [])];
    const carriers = consolidateCarrierShipments(archive.rows || []);
    const counterparties = [...(config.counterparties || [])];
    const numberKey = value => String(value || '').replace(/\s+/g, '').toLowerCase();
    const unique = values => [...new Set(values.map(value => String(value || '').trim()).filter(Boolean))].slice(0,100);
    let learned = 0;
    for (const row of rows) {
      const schet = String(row.schet || '').trim().toUpperCase();
      const order = orders.find(item => String(item.schet || '').trim().toUpperCase() === schet);
      const number = numberKey(row.expeditor);
      const carrier = carriers.find(item => [item.expeditorNumber,item.track,item.cargoTracking].some(value => numberKey(value) === number));
      const bitrixName = String(order?.client || '').trim();
      const carrierName = String(carrier?.client || '').trim();
      if (!bitrixName || !carrierName) continue;
      const names = [bitrixName, carrierName];
      let index = counterparties.findIndex(item => [item.name,...(item.aliases || []),...(item.contacts || [])]
        .some(value => names.some(name => normalizeMatchText(value) === normalizeMatchText(name))));
      const now = new Date().toISOString();
      if (index < 0) {
        counterparties.unshift({ id:crypto.randomUUID(), name:bitrixName,
          inn:String(order?.clientInn || carrier?.clientInn || '').replace(/\D/g,''),
          aliases:unique(carrierName !== bitrixName ? [carrierName] : []), contacts:[], phones:[],
          learnedFrom:'manual-expeditor', learnedAccount:schet, createdAt:now, updatedAt:now });
        learned += 1;
      } else {
        const current = counterparties[index];
        const aliases = unique([...(current.aliases || []), ...names.filter(name => normalizeMatchText(name) !== normalizeMatchText(current.name))]);
        if (aliases.length !== (current.aliases || []).length) learned += 1;
        counterparties[index] = { ...current, aliases, learnedFrom:current.learnedFrom || 'manual-expeditor', learnedAccount:schet, updatedAt:now };
      }
    }
    return { counterparties, learned };
  } catch (error) {
    console.error('[counterparties] Не удалось обучить справочник:', error.message);
    return { counterparties:[...(config.counterparties || [])], learned:0 };
  }
}

function cleanAccountNumber(value) {
  const match = String(value || '').toUpperCase().match(/[А-ЯЁA-Z]{1,8}-\d+/);
  return match ? match[0] : String(value || '').trim();
}

function consolidateBitrixAdditions(rows) {
  const byAccount = new Map();
  rows.forEach(row => {
    const account = cleanAccountNumber(row.schet);
    if (account && !byAccount.has(account)) byAccount.set(account, row);
  });
  const removed = new Set();
  rows.forEach(row => {
    const raw = String(row.schet || '');
    const addition = raw.match(/добавка\s+к\s+([А-ЯЁA-Z]{1,8}-\d+)/i);
    if (!addition) { row.schet = cleanAccountNumber(raw); return; }
    const targetAccount = addition[1].toUpperCase();
    const target = byAccount.get(targetAccount);
    if (!target || target === row) {
      row.schet = cleanAccountNumber(raw);
      row.additionTo = targetAccount;
      return;
    }
    target.sum = Number(target.sum || 0) + Number(row.sum || 0);
    target.additionBitrixIds = [...(target.additionBitrixIds || []), row.bitrixId].filter(Boolean);
    target.additionAccounts = [...(target.additionAccounts || []), cleanAccountNumber(raw)].filter(Boolean);
    removed.add(row);
  });
  return rows.filter(row => !removed.has(row));
}

let backgroundRefreshRunning=false;
async function refreshDashboardSnapshotInBackground() {
  if(backgroundRefreshRunning) return;
  backgroundRefreshRunning=true;
  try {
    const previous=fs.existsSync(DASHBOARD_SNAPSHOT_FILE)?JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE,'utf8')):{orders:[],ourDeliveries:[],selfPickups:[],sheetLogisticsRows:[],unmatchedMatchOrders:[]};
    let sheetLogisticsRows=Array.isArray(previous.sheetLogisticsRows)?previous.sheetLogisticsRows:[];
    try {
      const sheet=await fetchGoogleLogistics(true);
      if(Array.isArray(sheet.deliveries) && sheet.deliveries.length) sheetLogisticsRows=sheet.deliveries;
    } catch(error) {
      // Keep the last good trip sheet when Google is temporarily unavailable.
      console.error('[snapshot] Таблица рейсов временно недоступна:',error.message);
    }
    const needsFullArchive=!fs.existsSync(CARRIER_ARCHIVE_FILE) || !JSON.parse(fs.readFileSync(CARRIER_ARCHIVE_FILE,'utf8')).full;
    const archive=await refreshCarrierArchive(needsFullArchive);
    let fresh;
    try {
      fresh=await fetchBitrixOrders(true);
    } catch(error) {
      // Re-run matching against the last good Bitrix snapshot even when
      // Bitrix is temporarily unavailable. This keeps manual and improved
      // matching rules usable without freezing or discarding saved data.
      console.error('[snapshot] Bitrix24 временно недоступен, используется сохранённый снимок:',error.message);
      fresh={
        orders:(previous.orders||[]).filter(item=>item.bitrixId&&item.shipmentType==='Транспортная компания'),
        own:(previous.ourDeliveries||[]).filter(item=>item.bitrixId),
        pickups:(previous.selfPickups||[]).filter(item=>item.bitrixId),
      };
    }
    fresh.orders=consolidateBitrixAdditions(fresh.orders);
    fresh.own=consolidateBitrixAdditions(fresh.own);
    fresh.pickups=consolidateBitrixAdditions(fresh.pickups);
    const ourDeliveryNumbers=new Set(sheetLogisticsRows.filter(row=>/наша\s+доставка/i.test(row.deliveryType||'')).map(row=>String(row.orderNumber||'').replace(/^0+/,'')));
    const isSheetOurDelivery=item=>{
      const match=String(item.schet||'').match(/(\d+)(?!.*\d)/);
      return Boolean(match&&ourDeliveryNumbers.has(String(match[1]).replace(/^0+/,'')));
    };
    const movedToOurDelivery=fresh.orders.filter(isSheetOurDelivery);
    fresh.orders=fresh.orders.filter(item=>!isSheetOurDelivery(item));
    fresh.own=consolidateBitrixAdditions([...fresh.own,...movedToOurDelivery.map(item=>({...item,shipmentType:'Доставка',tk:'',carrierHint:''}))]);
    const oldOrders=new Map((previous.orders||[]).filter(item=>item.bitrixId).map(item=>[String(item.bitrixId),item]));
    const oldOur=new Map((previous.ourDeliveries||[]).filter(item=>item.bitrixId).map(item=>[String(item.bitrixId),item]));
    const preserveCarrier=(old,item)=>old?{...old,schet:item.schet,client:item.client,sum:item.sum,date:item.date,shipmentDate:item.shipmentDate,stage:item.stage,city:item.city,addr:item.addr,shippingInfo:item.shippingInfo,carrierHint:item.carrierHint,tk:old.carrierConnected?old.tk:item.tk,payer:item.payer,payerType:item.payerType,payerTypeLabel:item.payerTypeLabel,contactPerson:item.contactPerson,clientPhone:item.clientPhone,bitrixPhotos:item.bitrixPhotos,bitrixUrl:item.bitrixUrl}:item;
    const contractedIds=new Set(oldOur.keys());
    const orders=fresh.orders.filter(item=>!contractedIds.has(String(item.bitrixId))).map(item=>preserveCarrier(oldOrders.get(String(item.bitrixId)),item));
    const standalone=(previous.orders||[]).filter(item=>!item.bitrixId && item.client && /акфикс[\s-]*рус/i.test(item.client));
    const ourDeliveries=[...fresh.own.map(item=>preserveCarrier(oldOur.get(String(item.bitrixId)),item)),...fresh.orders.filter(item=>contractedIds.has(String(item.bitrixId))).map(item=>preserveCarrier(oldOur.get(String(item.bitrixId)),item))];
    const oldPickups=new Map((previous.selfPickups||[]).filter(row=>row.bitrixId).map(row=>[String(row.bitrixId),row]));
    const pickups=fresh.pickups.map(item=>{
      const merged=preserveCarrier(oldPickups.get(String(item.bitrixId)),item);
      const taken=String(item.stage||'')==='Груз отправлен';
      const ready=String(item.stage||'')==='Груз проверен';
      const rawDate=String(item.date||item.shipmentDate||'');
      const dateMatch=rawDate.match(/^(\d{2})\.(\d{2})\.(\d{4})/);
      const readyDate=dateMatch?new Date(Number(dateMatch[3]),Number(dateMatch[2])-1,Number(dateMatch[1])):new Date(rawDate);
      const daysWaiting=!taken&&!Number.isNaN(readyDate.getTime())?Math.max(0,Math.floor((Date.now()-readyDate.getTime())/86400000)):0;
      return {...merged,svStatus:taken?'taken':(ready?'ready':'waiting'),svStatusLabel:taken?'Забрали':(ready?'Готово к выдаче':'Ожидает готовности'),daysWaiting};
    });
    const matchedOrders=matchOrdersOnServer(orders,archive.rows||[]);
    const incoming=consolidateCarrierShipments(archive.rows||[]).filter(item=>/акфикс[\s-]*рус/i.test(item.client||'')&&!usedSnapshotCarrier(item,matchedOrders));
    const finalOrders=[...matchedOrders,...consolidateCarrierShipments([...standalone,...incoming])];
    const unmatchedMatchOrders=finalOrders.filter(item=>item.bitrixId&&item.carrierConnected===false&&/байкал|делов|мега/i.test(item.carrierHint||item.tk||''));
    let cdekSamples=[];
    try { cdekSamples=(await fetchBitrixCdekSamples(true)).shipments||[]; }
    catch(error) { console.error('[snapshot] СДЭК/образцы временно недоступны:',error.message); cdekSamples=previous.cdekShipments?.filter(item=>item.sourceType==='Отправка образцов')||[]; }
    const cdekMain=finalOrders.filter(item=>item.bitrixId&&isCdekOrder(item)).map(item=>({...item,tk:'СДЭК',carrierHint:'СДЭК',sourceType:'Отгрузки'}));
    const cdekShipments=[...cdekMain,...cdekSamples];
    writeDashboardSnapshot({...previous,orders:finalOrders,ourDeliveries,selfPickups:pickups,sheetLogisticsRows,unmatchedMatchOrders,cdekShipments});
    console.log(`[snapshot] Bitrix24 обновлён: ${orders.length+ourDeliveries.length+pickups.length} заказов`);
  } catch(error) { console.error('[snapshot] Фоновое обновление не выполнено:',error.message); }
  finally { backgroundRefreshRunning=false; }
}

async function refreshBitrixSnapshotQuick() {
  try {
    const previous=fs.existsSync(DASHBOARD_SNAPSHOT_FILE)?JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE,'utf8')):{orders:[],ourDeliveries:[],selfPickups:[],sheetLogisticsRows:[],unmatchedMatchOrders:[],cdekShipments:[]};
    const fresh=await fetchBitrixOrders(true);
    fresh.orders=consolidateBitrixAdditions(fresh.orders);
    fresh.own=consolidateBitrixAdditions(fresh.own);
    fresh.pickups=consolidateBitrixAdditions(fresh.pickups);

    const mergeBitrixRows=(incoming,oldRows)=>{
      const oldById=new Map((oldRows||[]).filter(row=>row.bitrixId).map(row=>[String(row.bitrixId),row]));
      return (incoming||[]).map(row=>{
        const old=oldById.get(String(row.bitrixId));
        if(!old) return row;
        const merged={...old,...row};
        // Bitrix owns the order fields; the carrier fields remain valid until
        // the slower carrier worker refreshes them.
        // Название ТК у ещё не сопоставленного заказа принадлежит Bitrix24 и
        // может уточняться в комментарии. Сохраняем старое `tk` только после
        // фактического соединения с записью перевозчика.
        const carrierFields=['carrierConnected','source','expeditorNumber','track','cargoTracking','cargoNumber','deliveryStatus','tkStatus','deliveryCost','deliveryDate','actualDelivery','terminal','terminalAddress','weight','volume','places','cargoPhotos'];
        carrierFields.forEach(key=>{ if(old[key]!==undefined&&old[key]!==null&&old[key]!=='') merged[key]=old[key]; });
        if(old.carrierConnected && old.tk) merged.tk=old.tk;
        return merged;
      });
    };

    const standalone=(previous.orders||[]).filter(row=>!row.bitrixId);
    const orders=[...mergeBitrixRows(fresh.orders,previous.orders),...standalone];
    const ourDeliveries=mergeBitrixRows(fresh.own,previous.ourDeliveries);
    const selfPickups=mergeBitrixRows(fresh.pickups,previous.selfPickups).map(item=>{
      const taken=String(item.stage||'')==='Груз отправлен';
      const ready=String(item.stage||'')==='Груз проверен';
      return {...item,svStatus:taken?'taken':(ready?'ready':'waiting'),svStatusLabel:taken?'Забрали':(ready?'Готово к выдаче':'Ожидает готовности')};
    });
    const unmatchedMatchOrders=orders.filter(item=>item.bitrixId&&item.carrierConnected===false&&/байкал|делов|мега/i.test(item.carrierHint||item.tk||''));
    const cdekSaved=(previous.cdekShipments||[]).filter(item=>item.sourceType==='Отправка образцов');
    const cdekMain=orders.filter(item=>item.bitrixId&&isCdekOrder(item)).map(item=>({...item,tk:'СДЭК',carrierHint:'СДЭК',sourceType:'Отгрузки'}));
    writeDashboardSnapshot({...previous,orders,ourDeliveries,selfPickups,unmatchedMatchOrders,cdekShipments:[...cdekMain,...cdekSaved]});
    console.log(`[snapshot:bitrix] Быстрое обновление: ${fresh.orders.length+fresh.own.length+fresh.pickups.length} заказов; начальная стадия: ${fresh.startStage}`);
  } catch(error) {
    console.error('[snapshot:bitrix] Быстрое обновление не выполнено:',error.message);
  }
}

let refreshWorker = null;
function startSnapshotRefreshWorker(mode='full') {
  if (refreshWorker) return;
  refreshWorker = fork(__filename, [], {
    env: { ...process.env, AKFIX_REFRESH_ONCE:'1', AKFIX_REFRESH_MODE:mode },
    stdio: 'inherit',
  });
  refreshWorker.on('exit', (code) => {
    if (code) console.error(`[snapshot] Фоновый процесс завершился с кодом ${code}`);
    refreshWorker = null;
  });
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let body = '';
    req.on('data', chunk => {
      body += chunk;
      if (body.length > 32 * 1024 * 1024) reject(new Error('Слишком большой запрос'));
    });
    req.on('end', () => {
      try { resolve(body ? JSON.parse(body) : {}); } catch (_) { reject(new Error('Некорректный JSON')); }
    });
    req.on('error', reject);
  });
}

function safeExcelText(value) {
  const text = String(value ?? '').trim();
  return /^[=+\-@]/.test(text) ? `'${text}` : text;
}

function parseExcelDate(value) {
  const text = String(value || '').trim();
  let match = text.match(/^(\d{2})\.(\d{2})\.(\d{4})/);
  if (match) return new Date(Number(match[3]), Number(match[2]) - 1, Number(match[1]), 12);
  match = text.match(/^(\d{4})-(\d{2})-(\d{2})/);
  if (match) return new Date(Number(match[1]), Number(match[2]) - 1, Number(match[3]), 12);
  return null;
}

async function buildLogisticsWorkbook(payload = {}) {
  // Excel is an optional export feature. Keep the dashboard available even
  // while local dependencies are being restored.
  const ExcelJS = require('exceljs');
  const workbook = new ExcelJS.Workbook();
  workbook.creator = 'Akfix Logistics';
  workbook.created = new Date();
  const isMatching = payload.type === 'matching';
  const sheet = workbook.addWorksheet(isMatching ? 'Сопоставление' : 'Транспортные отправки', {
    views: [{ state: 'frozen', ySplit: 3, xSplit: 1, showGridLines: false }],
    pageSetup: { orientation: 'landscape', fitToPage: true, fitToWidth: 1, fitToHeight: 0 },
  });
  const columns = isMatching ? [
    ['№','number',7], ['Счёт / сделка','deal',20], ['Клиент','client',34], ['Город','city',22],
    ['ТК из Bitrix24','tk',23], ['Дата отгрузки','shipped',17], ['Экспедиторская расписка','expeditor',30],
  ] : [
    ['Счёт / сделка','deal',18], ['Клиент','client',31], ['Отправитель','sender',28],
    ['Плановая отгрузка','planned',16], ['Дата отправки','shipped',16], ['Дата доставки','delivered',16],
    ['Город','city',22], ['Статус доставки','deliveryStatus',21], ['Стадия Bitrix24','stage',21],
    ['Транспортная компания','tk',22], ['Экспедиторская расписка','expeditor',24], ['Номер перевозки','cargo',20],
    ['Водитель до ТК','localDriver',24], ['Затраты до ТК','firstMileCost',17], ['Плательщик','payer',22],
    ['Стоимость доставки','deliveryCost',20], ['Сумма заказа','orderSum',18],
  ];
  const lastColumn = sheet.getColumn(columns.length).letter;
  sheet.mergeCells(`A1:${lastColumn}1`);
  sheet.getCell('A1').value = isMatching ? 'AKFIX · Сопоставление отправок' : 'AKFIX · Транспортные отправки';
  sheet.getCell('A1').font = { name: 'Arial', size: 18, bold: true, color: { argb: 'FFFFFFFF' } };
  sheet.getCell('A1').fill = { type: 'pattern', pattern: 'solid', fgColor: { argb: 'FFE51B23' } };
  sheet.getCell('A1').alignment = { vertical: 'middle', horizontal: 'left' };
  sheet.getRow(1).height = 34;
  sheet.mergeCells(`A2:${lastColumn}2`);
  sheet.getCell('A2').value = `Период: ${safeExcelText(payload.period || 'текущий фильтр')} · Строк: ${Array.isArray(payload.rows) ? payload.rows.length : 0} · Сформировано: ${new Date().toLocaleString('ru-RU')}`;
  sheet.getCell('A2').font = { name: 'Arial', size: 10, color: { argb: 'FF64748B' } };
  sheet.getCell('A2').alignment = { vertical: 'middle' };
  sheet.getRow(2).height = 23;
  sheet.getRow(3).values = columns.map(([title]) => title);
  sheet.getRow(3).height = 28;
  sheet.getRow(3).eachCell(cell => {
    cell.font = { name: 'Arial', size: 10, bold: true, color: { argb: 'FFFFFFFF' } };
    cell.fill = { type: 'pattern', pattern: 'solid', fgColor: { argb: 'FF18243A' } };
    cell.alignment = { vertical: 'middle', horizontal: 'center', wrapText: true };
  });
  columns.forEach(([,key,width], index) => {
    const column = sheet.getColumn(index + 1);
    column.key = key;
    column.width = width;
  });
  const dateKeys = new Set(['planned','shipped','delivered']);
  const moneyKeys = new Set(['firstMileCost','deliveryCost','orderSum']);
  for (const source of Array.isArray(payload.rows) ? payload.rows.slice(0, 10000) : []) {
    const values = columns.map(([,key]) => {
      if (dateKeys.has(key)) return parseExcelDate(source[key]) || null;
      if (moneyKeys.has(key)) return Number(source[key] || 0);
      return safeExcelText(source[key]);
    });
    const row = sheet.addRow(values);
    row.height = 31;
    row.eachCell((cell, colNumber) => {
      const key = columns[colNumber - 1][1];
      cell.font = { name: 'Arial', size: 9, color: { argb: 'FF172033' } };
      cell.alignment = { vertical: 'middle', horizontal: moneyKeys.has(key) ? 'right' : 'left', wrapText: ['client','sender','city','payer'].includes(key) };
      cell.border = { bottom: { style: 'thin', color: { argb: 'FFE2E8F0' } } };
      if (dateKeys.has(key)) cell.numFmt = 'dd.mm.yyyy';
      if (moneyKeys.has(key)) cell.numFmt = '#,##0.00 [$₽-ru-RU]';
    });
    if (!isMatching) {
      const statusCell = row.getCell(8);
      const statusText = String(statusCell.value || '').toLowerCase();
      if (/выдан|доставлен|прибыл/.test(statusText)) {
        statusCell.fill = { type: 'pattern', pattern: 'solid', fgColor: { argb: 'FFDDF6E8' } };
        statusCell.font = { name: 'Arial', size: 9, bold: true, color: { argb: 'FF16834A' } };
      } else if (/нет данных|ошиб|просроч/.test(statusText)) {
        statusCell.fill = { type: 'pattern', pattern: 'solid', fgColor: { argb: 'FFFDE7E8' } };
        statusCell.font = { name: 'Arial', size: 9, bold: true, color: { argb: 'FFC81924' } };
      }
    }
  }
  const lastRow = Math.max(3, sheet.rowCount);
  sheet.autoFilter = { from: 'A3', to: `${lastColumn}${lastRow}` };
  if (!isMatching) {
    sheet.getColumn(14).numFmt = '#,##0.00 [$₽-ru-RU]';
    sheet.getColumn(16).numFmt = '#,##0.00 [$₽-ru-RU]';
    sheet.getColumn(17).numFmt = '#,##0.00 [$₽-ru-RU]';
  } else {
    sheet.getColumn(7).fill = { type: 'pattern', pattern: 'solid', fgColor: { argb: 'FFFFF7D6' } };
  }
  return workbook.xlsx.writeBuffer();
}

function stripHtml(value) {
  return String(value || '')
    .replace(/<br\s*\/?\s*>/gi, ' ')
    .replace(/<[^>]*>/g, ' ')
    .replace(/&nbsp;/gi, ' ')
    .replace(/&amp;/gi, '&')
    .replace(/&quot;/gi, '"')
    .replace(/&#39;/gi, "'")
    .replace(/\s+/g, ' ')
    .trim();
}

function parseCsv(text) {
  const rows = [];
  let row = [], cell = '', quoted = false;
  const source = String(text || '').replace(/^\uFEFF/, '');
  for (let index = 0; index < source.length; index += 1) {
    const char = source[index];
    if (quoted) {
      if (char === '"' && source[index + 1] === '"') { cell += '"'; index += 1; }
      else if (char === '"') quoted = false;
      else cell += char;
    } else if (char === '"') quoted = true;
    else if (char === ',') { row.push(cell); cell = ''; }
    else if (char === '\n') { row.push(cell.replace(/\r$/, '')); rows.push(row); row = []; cell = ''; }
    else cell += char;
  }
  if (cell || row.length) { row.push(cell.replace(/\r$/, '')); rows.push(row); }
  return rows;
}

function parseSheetMoney(value) {
  const normalized = String(value || '').replace(/\u00a0/g, '').replace(/[^\d,-]/g, '').replace(',', '.');
  return Number(normalized) || 0;
}

function normalizeSheetPerson(value) {
  return String(value || '').toLowerCase().replace(/ё/g, 'е').replace(/[^a-zа-я0-9]+/gi, ' ').replace(/\s+/g, ' ').trim();
}

async function fetchGoogleLogistics(force = false) {
  if (!force && googleLogisticsCache.data && googleLogisticsCache.expiresAt > Date.now()) return googleLogisticsCache.data;
  const response = await fetch(GOOGLE_LOGISTICS_CSV, { signal: AbortSignal.timeout(30000) });
  if (!response.ok) throw new Error(`Google Таблица вернула HTTP ${response.status}`);
  const rows = parseCsv(await response.text());
  const deliveries = [];
  const summaries = [];
  let inheritedClient = '';
  for (const cells of rows.slice(3)) {
    const date = String(cells[1] || '').trim();
    const client = String(cells[3] || '').trim();
    if (client) inheritedClient = client;
    const orderNumber = String(cells[4] || '').trim();
    const driver = String(cells[11] || '').trim();
    const deliveryType = String(cells[12] || '').trim();
    // Способ доставки иногда остаётся пустым, хотя номер счёта и водитель уже
    // назначены. Такая строка всё равно нужна панели; тип берём из Bitrix24.
    if (/^\d+$/.test(orderNumber) && date && driver) {
      deliveries.push({
        date, client: client || inheritedClient, orderNumber, requestNumber: String(cells[5] || '').trim(),
        warehouse: String(cells[6] || '').trim(), documents: String(cells[7] || '').trim(),
        rework: String(cells[8] || '').trim(), status: String(cells[10] || '').trim(), driver, deliveryType,
        carrierCost: parseSheetMoney(cells[13]), orderSum: parseSheetMoney(cells[14]), logisticsCost: 0,
      });
    }
    const summaryDriver = String(cells[26] || '').trim();
    const logisticsCost = parseSheetMoney(cells[29]);
    if (date && summaryDriver && logisticsCost > 0) summaries.push({ date, driver: summaryDriver, logisticsCost });
  }
  for (const summary of summaries) {
    const driverKey = normalizeSheetPerson(summary.driver);
    const group = deliveries.filter(item => item.date === summary.date && normalizeSheetPerson(item.driver) === driverKey);
    const groupSum = group.reduce((sum, item) => sum + Number(item.orderSum || 0), 0);
    let allocated = 0;
    group.forEach((item, index) => {
      const amount = index === group.length - 1
        ? Math.max(0, summary.logisticsCost - allocated)
        : Math.round((groupSum > 0 ? summary.logisticsCost * item.orderSum / groupSum : summary.logisticsCost / Math.max(1, group.length)) * 100) / 100;
      item.logisticsCost = amount;
      item.logisticsShare = groupSum > 0 ? item.orderSum / groupSum : 1 / Math.max(1, group.length);
      item.logisticsGroupSum = groupSum;
      item.logisticsTripCost = summary.logisticsCost;
      allocated += amount;
    });
  }
  const data = { ok: true, spreadsheetId: '18H4xoO7DFMsIml68G-Ama_fxjc3EW8-tbcKBCtAuuC4', count: deliveries.length, deliveries, summaries: summaries.length };
  // Таблица «Отгрузка» является источником суммы заказа, водителя и затрат
  // первой мили. Держим снимок на сервере десять минут, чтобы браузеры
  // сотрудников никогда не обращались к Google напрямую.
  googleLogisticsCache = { expiresAt: Date.now() + 10 * 60 * 1000, data };
  return data;
}

function normalizeBitrixWebhook(value) {
  const webhook = String(value || '').trim().replace(/\/+$/, '');
  if (!/^https:\/\/[^/]+\.bitrix24\.ru\/rest\/\d+\/[a-z0-9]+$/i.test(webhook)) {
    throw new Error('Некорректный адрес вебхука Bitrix24');
  }
  return `${webhook}/`;
}

function extractCarrierHint(value) {
  const text = String(value || '').replace(/\s+/g, ' ').trim();
  // В комментарии могут раньше встречаться названия клиента вроде «ТК Папа Карло»,
  // а фактический перевозчик указывается в конце. Известную ТК ищем по всему полю.
  if (/делов(?:ые|ая)\s+лини/i.test(text)) return 'Деловые Линии';
  if (/байкал(?:\s*[-–—]?\s*сервис)?/i.test(text)) return 'Байкал Сервис';
  if (/мега\s*[-–—]?\s*транс/i.test(text)) return 'Мегатранс';
  // В Bitrix24 эти перевозчики часто записаны обычным текстом без префикса
  // «ТК»: «ООО Транспортная Компания Алтайтранс» или «Норд Вил до терминала».
  if (/алтай\s*[-–—]?\s*транс/i.test(text)) return 'АлтайТранс';
  if (/норд\s*[-–—]?\s*вил(?:л)?/i.test(text)) return 'НордВил';
  const match = text.match(/(?:^|[^а-яёa-z0-9])тк\s*[:\-]?\s*([^,;\n]+)/i);
  if (!match) return '';
  const stopWords = /^(до|от|через|адрес|терминал|г\.?|город|схема|проезд|доставка|по|на|в|склад|работает|грузополучатель|получатель|контакт|телефон)$/i;
  const words = match[1].trim().split(/\s+/);
  const carrier = [];
  for (const rawWord of words) {
    const word = rawWord.replace(/^["«(]+|["»).:]+$/g, '');
    if (!word || stopWords.test(word)) break;
    carrier.push(word);
    if (carrier.length >= 3) break;
  }
  const result = carrier.join(' ').trim();
  if (/мега\s*транс/i.test(result)) return 'Мегатранс';
  if (/байкал/i.test(result)) return 'Байкал Сервис';
  if (/делов(ые|ая)\s+лини/i.test(result)) return 'Деловые Линии';
  if (/алтай\s*[-–—]?\s*транс/i.test(result)) return 'АлтайТранс';
  if (/норд\s*[-–—]?\s*вил(?:л)?/i.test(result)) return 'НордВил';
  return result;
}

async function bitrixCall(webhook, method, params = {}) {
  let lastError;
  for(let attempt=1;attempt<=3;attempt+=1){
    try{
      const response = await fetch(`${normalizeBitrixWebhook(webhook)}${method}.json`, {
        method: 'POST',
        headers: { Accept: 'application/json', 'Content-Type': 'application/json; charset=utf-8' },
        body: JSON.stringify(params),
        signal: AbortSignal.timeout(45000),
      });
      const data = await response.json().catch(() => ({}));
      if((response.status===429||response.status>=500)&&attempt<3){await new Promise(resolve=>setTimeout(resolve,attempt*1200));continue;}
      if (!response.ok || data.error) throw new Error(stripHtml(data.error_description || data.error || `Bitrix24 вернул HTTP ${response.status}`));
      return data;
    }catch(error){
      lastError=error;
      if(attempt<3&&/fetch failed|timeout|econn|socket/i.test(`${error.message} ${error.cause?.code||''}`)){
        await new Promise(resolve=>setTimeout(resolve,attempt*1200));
        continue;
      }
      throw error;
    }
  }
  throw lastError;
}

async function bitrixPhotoItem(webhook, itemId) {
  const key = String(itemId);
  const cached = bitrixPhotoItemCache.get(key);
  if (cached && cached.expiresAt > Date.now()) return cached.promise;
  // One card can contain many photos. All browser image requests share one
  // crm.item.get call instead of hitting Bitrix24 eight times in parallel.
  const promise = bitrixCall(webhook, 'crm.item.get', { entityTypeId:1052, id:itemId })
    .then(result => result.result?.item || {})
    .catch(error => { bitrixPhotoItemCache.delete(key); throw error; });
  bitrixPhotoItemCache.set(key, { expiresAt:Date.now() + 2 * 60 * 1000, promise });
  return promise;
}

async function fetchBitrixPhoto(url) {
  let lastError;
  for (let attempt = 1; attempt <= 3; attempt += 1) {
    try {
      const response = await fetch(url, { signal:AbortSignal.timeout(45000) });
      if ((response.status === 429 || response.status >= 500) && attempt < 3) {
        await new Promise(resolve => setTimeout(resolve, attempt * 800));
        continue;
      }
      if (!response.ok) throw new Error(`Bitrix24 вернул HTTP ${response.status}`);
      return response;
    } catch (error) {
      lastError = error;
      if (attempt < 3 && /fetch failed|timeout|econn|socket/i.test(`${error.message} ${error.cause?.code || ''}`)) {
        await new Promise(resolve => setTimeout(resolve, attempt * 800));
        continue;
      }
      throw error;
    }
  }
  throw lastError;
}

async function parseInvoiceQuantity(content) {
  const parsed = await pdfParse(content);
  const text = String(parsed.text || '').replace(/\u00a0/g, ' ');
  const values = [];
  for (const rawLine of text.split(/\r?\n/)) {
    const line = rawLine.replace(/\s+/g, ' ').trim();
    // Current 1C invoice rows start with their position number.  The pieces
    // column is immediately before "шт"; values after it are boxes, price,
    // amount, weight and volume and must never be counted as pieces.
    const row = line.match(/^\d+\s+.+\s(\d[\d ]*(?:[.,]\d+)?)\s*шт(?:\s|$)/iu);
    // pdf-parse flattens some 1C tables to e.g. "12.2724шт1,00":
    // series 12.27, 24 pieces, 1.00 boxes. Capture only the digits after
    // the MM.YY series and before "шт".
    const compact = line.match(/(?:^|\D)\d{2}[.,]\d{2}(\d+(?:[.,]\d+)?)шт/iu);
    const rawValue = row?.[1] || compact?.[1];
    if (!rawValue) continue;
    const value = Number(rawValue.replace(/\s/g, '').replace(',', '.'));
    if (Number.isFinite(value) && value >= 0 && value <= 1000000) values.push(value);
  }
  // Older exported invoices use a compact warehouse-reservation phrase.
  if (!values.length) {
    for (const match of text.matchAll(/Резервировать на складе\s+(\d+(?:[.,]\d+)?)\s*шт\b/giu)) {
      const value = Number(match[1].replace(',', '.'));
      if (Number.isFinite(value) && value >= 0 && value <= 1000000) values.push(value);
    }
  }
  if (!values.length) throw new Error('В счёте не найдена колонка количества');
  const quantity = values.reduce((sum, value) => sum + value, 0);
  return { quantity, readAt:Date.now() };
}

async function invoiceStatsForItems(webhook, requestedItems) {
  const items = Array.isArray(requestedItems) ? requestedItems.slice(0, 250) : [];
  let cursor = 0;
  const result = new Array(items.length);
  const worker = async () => {
    while (cursor < items.length) {
      const index = cursor++;
      const itemId = Number(items[index]?.itemId);
      const fileId = Number(items[index]?.fileId);
      if (!Number.isFinite(itemId) || !Number.isFinite(fileId)) { result[index] = { itemId, fileId, error:'Некорректный идентификатор' }; continue; }
      if (invoiceQuantityCache[fileId]) { result[index] = { itemId, fileId, ...invoiceQuantityCache[fileId] }; continue; }
      try {
        const item = await bitrixPhotoItem(webhook, itemId);
        const files = Array.isArray(item[BITRIX_INVOICE_FIELD]) ? item[BITRIX_INVOICE_FIELD] : (item[BITRIX_INVOICE_FIELD] ? [item[BITRIX_INVOICE_FIELD]] : []);
        const file = files.find(entry => Number(entry?.id || entry) === fileId);
        if (!file?.urlMachine) throw new Error('Счёт не найден');
        const response = await fetchBitrixPhoto(file.urlMachine);
        const stats = await parseInvoiceQuantity(Buffer.from(await response.arrayBuffer()));
        invoiceQuantityCache[fileId] = stats;
        writeJsonAtomic(INVOICE_QUANTITY_CACHE_FILE, invoiceQuantityCache);
        result[index] = { itemId, fileId, ...stats };
      } catch (error) { result[index] = { itemId, fileId, error:error.message }; }
    }
  };
  await Promise.all(Array.from({ length:Math.min(4, items.length) }, worker));
  return result;
}

async function testBitrixConnection(webhook) {
  const [profile, fields, stages] = await Promise.all([
    bitrixCall(webhook, 'profile'),
    bitrixCall(webhook, 'crm.item.fields', { entityTypeId: 1052 }),
    bitrixCall(webhook, 'crm.status.list', { filter: { ENTITY_ID: 'DYNAMIC_1052_STAGE_31' } }),
  ]);
  return { profile: profile.result, fields: fields.result, stages: stages.result || [] };
}

async function fetchBitrixOrders(force = false) {
  if (!force && bitrixCache.data && bitrixCache.expiresAt > Date.now()) return bitrixCache.data;
  const config = loadConfig();
  if (!config.bitrixWebhook) throw new Error('Bitrix24 не настроен');
  const { stages } = await testBitrixConnection(config.bitrixWebhook);
  // Передаём заказ в мониторинг ещё до начала сборки. Старое название —
  // запасной вариант на случай отличий в настройках воронки Bitrix24.
  const startStage = stages.find(stage => /передан(?:о)? на склад/i.test(stage.NAME))
    || stages.find(stage => /передан на сборку/i.test(stage.NAME));
  if (!startStage) throw new Error('В сопровождении продаж не найдена начальная стадия «Передан на склад»');
  const startSort = Number(startStage.SORT || 0);
  const processStages = stages.filter(stage => {
    const sort = Number(stage.SORT || 0);
    return sort >= startSort && sort <= 110;
  });
  const stageIds = processStages.map(stage => stage.STATUS_ID);
  const stageNames = Object.fromEntries(processStages.map(stage => [stage.STATUS_ID, stage.NAME]));
  const select = [
    'id','title','stageId','opportunity','currencyId','companyId','contactId','createdTime','updatedTime',
    'ufCrm19_1751013569410','ufCrm19_1751013649357','ufCrm19_1751013757786','ufCrm19_1751013854311',
    'ufCrm19_1751013980915','ufCrm19_1751014010938','ufCrm19_1751375632078','ufCrm19_1757589501142',
    'ufCrm19_1773996167987', ...BITRIX_PHOTO_FIELDS
  ];
  const deals = [];
  for (const stageId of stageIds) {
    let start = 0;
    do {
      const page = await bitrixCall(config.bitrixWebhook, 'crm.item.list', {
        entityTypeId: 1052, order: { id: 'DESC' }, filter: { categoryId: 31, stageId }, select, start,
      });
      deals.push(...(page.result?.items || []));
      start = Number.isFinite(Number(page.next)) ? Number(page.next) : -1;
    } while (start >= 0 && deals.length < 10000);
    if (deals.length >= 10000) break;
  }

  const companyIds = [...new Set(deals.map(deal => Number(deal.companyId)).filter(Boolean))];
  const companies = {};
  for (let offset = 0; offset < companyIds.length; offset += 50) {
    const page = await bitrixCall(config.bitrixWebhook, 'crm.company.list', {
      filter: { ID: companyIds.slice(offset, offset + 50) }, select: ['ID','TITLE'], start: 0,
    });
    for (const company of page.result || []) companies[company.ID] = company.TITLE;
  }
  const enumValue = (value, values) => values[String(Array.isArray(value) ? value[0] : value)] || '';
  const shipmentValues = { '1373': 'Самовывоз', '1375': 'Доставка', '1377': 'Транспортная компания' };
  const payerValues = { '1379': 'Мы', '1381': 'Клиент' };
  const mapped = deals.map(deal => {
    const shipmentType = enumValue(deal.ufCrm19_1751013757786, shipmentValues);
    const payerChoice = enumValue(deal.ufCrm19_1751013980915, payerValues);
    const address = deal.ufCrm19_1757589501142 || '';
    const shippingInfo = deal.ufCrm19_1751013649357 || '';
    const carrierHint = resolveCarrierAlias(extractCarrierHint(shippingInfo), config);
    const bitrixPhotos = BITRIX_PHOTO_FIELDS.flatMap(fieldName => {
      const value = deal[fieldName];
      const files = Array.isArray(value) ? value : (value ? [value] : []);
      return files.map(file => ({ fieldName, fileId:Number(file?.id || file) })).filter(file => Number.isFinite(file.fileId) && file.fileId > 0);
    });
    return {
      id: `bitrix-${deal.id}`, bitrixId: String(deal.id), schet: deal.ufCrm19_1751013569410 || deal.title || `Отгрузка ${deal.id}`,
      client: companies[deal.companyId] || deal.title || '', sender: 'ООО «АКФИКС-РУС»', sum: Number(deal.opportunity || 0),
      date: deal.ufCrm19_1751014010938 || '', shipmentDate: deal.ufCrm19_1751375632078 || '', deliveryDate: '',
      city: address, addr: address,
      deliveryStatus: '', stage: stageNames[deal.stageId] || deal.stageId, tk: shipmentType === 'Транспортная компания' ? (carrierHint || 'ТК не указана') : '',
      track: '', expeditorNumber: '', payer: payerChoice, payerType: payerChoice === 'Мы' ? 'our' : (payerChoice === 'Клиент' ? 'client' : 'other'),
      payerTypeLabel: payerChoice === 'Мы' ? 'Мы платим' : (payerChoice === 'Клиент' ? 'Клиент платит' : 'Не указан'),
      deliveryCost: 0, tkStatus: '', contactPerson: deal.ufCrm19_1751013854311 || '', clientPhone: deal.ufCrm19_1773996167987 || '',
      shippingInfo, carrierHint, carrierConnected: false, shipmentType, source: 'bitrix', bitrixPhotos, bitrixUrl: `${normalizeBitrixWebhook(config.bitrixWebhook).split('/rest/')[0]}/crm/type/1052/details/${deal.id}/`
    };
  });
  const data = {
    orders: consolidateBitrixAdditions(mapped.filter(item => item.shipmentType === 'Транспортная компания')),
    own: consolidateBitrixAdditions(mapped.filter(item => item.shipmentType === 'Доставка')),
    pickups: consolidateBitrixAdditions(mapped.filter(item => item.shipmentType === 'Самовывоз')),
    total: mapped.length, startStage: startStage.NAME, stages: processStages.map(stage => ({ id: stage.STATUS_ID, name: stage.NAME }))
  };
  bitrixCache = { expiresAt: Date.now() + 2 * 60 * 1000, data };
  return data;
}

function isCdekName(value) {
  return /(?:^|[^а-яёa-z])(?:сд[эе]к|cdek)(?:$|[^а-яёa-z])/i.test(String(value||''));
}

function isCdekOrder(item) {
  return isCdekName([
    item?.carrierHint,
    item?.tk,
    item?.shippingInfo,
    item?.city,
    item?.addr,
  ].filter(Boolean).join(' | '));
}

async function getCdekToken(config=loadConfig()) {
  if(cdekTokenCache.token && cdekTokenCache.expiresAt>Date.now()+60000) return cdekTokenCache.token;
  if(!config.cdekClientId || !config.cdekClientSecret) throw new Error('СДЭК не настроен');
  const body=new URLSearchParams({grant_type:'client_credentials',client_id:config.cdekClientId,client_secret:config.cdekClientSecret});
  const response=await fetch('https://api.cdek.ru/v2/oauth/token',{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body,signal:AbortSignal.timeout(30000)});
  const data=await response.json().catch(()=>({}));
  if(!response.ok || !data.access_token) throw new Error(stripHtml(data.message||data.error_description||data.error||`СДЭК вернул HTTP ${response.status}`));
  cdekTokenCache={token:data.access_token,expiresAt:Date.now()+Math.max(300,Number(data.expires_in||3600))*1000};
  return data.access_token;
}

async function fetchCdekOrderStatus(cdekNumber,config=loadConfig()) {
  const number=String(cdekNumber||'').trim();
  if(!number) return null;
  const token=await getCdekToken(config);
  const response=await fetch(`https://api.cdek.ru/v2/orders?cdek_number=${encodeURIComponent(number)}`,{headers:{Authorization:`Bearer ${token}`,Accept:'application/json'},signal:AbortSignal.timeout(30000)});
  if(response.status===404) return null;
  const data=await response.json().catch(()=>({}));
  if(!response.ok) throw new Error(stripHtml(data.message||data.error||`СДЭК вернул HTTP ${response.status}`));
  const entity=data.entity||data;
  const statuses=Array.isArray(entity.statuses)?entity.statuses:[];
  const current=statuses[statuses.length-1]||{};
  return {cdekUuid:entity.uuid||'',cdekNumber:String(entity.cdek_number||number),deliveryStatus:current.name||current.code||'',statusDate:current.date_time||'',deliveryCost:Number(entity.delivery_sum||0)};
}

async function fetchBitrixCdekSamples(force=false) {
  if(!force && cdekSamplesCache.data && cdekSamplesCache.expiresAt>Date.now()) return cdekSamplesCache.data;
  const config=loadConfig();
  if(!config.bitrixWebhook) throw new Error('Bitrix24 не настроен');
  const [fieldsResponse,stagesResponse]=await Promise.all([
    bitrixCall(config.bitrixWebhook,'crm.item.fields',{entityTypeId:1056}),
    bitrixCall(config.bitrixWebhook,'crm.status.list',{filter:{ENTITY_ID:'DYNAMIC_1056_STAGE_33'}}),
  ]);
  const fields=fieldsResponse.result?.fields||fieldsResponse.result||{};
  const stageNames=Object.fromEntries((stagesResponse.result||[]).map(stage=>[stage.STATUS_ID,stage.NAME]));
  const select=['id','title','stageId','opportunity','companyId','contactId','createdTime','updatedTime','ufCrm21_1750146252993','ufCrm21_1750146663742','ufCrm21_1750147040383','ufCrm21_1751015048770','ufCrm21_1751015108375','ufCrm21_1753872135589','ufCrm_1707397116579'];
  const items=[];
  let start=0;
  do {
    const page=await bitrixCall(config.bitrixWebhook,'crm.item.list',{entityTypeId:1056,order:{id:'DESC'},filter:{categoryId:33},select,start});
    items.push(...(page.result?.items||[]));
    start=Number.isFinite(Number(page.next))?Number(page.next):-1;
  } while(start>=0 && items.length<5000);
  const cdekItems=items.filter(item=>isCdekName(item.ufCrm21_1750146252993));
  const companyIds=[...new Set(cdekItems.map(item=>Number(item.companyId)).filter(Boolean))];
  const companies={};
  for(let offset=0;offset<companyIds.length;offset+=50){
    const page=await bitrixCall(config.bitrixWebhook,'crm.company.list',{filter:{ID:companyIds.slice(offset,offset+50)},select:['ID','TITLE'],start:0});
    for(const company of page.result||[]) companies[company.ID]=company.TITLE;
  }
  const rows=cdekItems.map(item=>({
    id:`cdek-sample-${item.id}`,bitrixId:String(item.id),sourceType:'Отправка образцов',source:'bitrix-cdek-samples',
    schet:item.title||`Образцы ${item.id}`,client:companies[item.companyId]||item.title||'',sum:Number(item.opportunity||0),
    tk:'СДЭК',carrierHint:'СДЭК',track:String(item.ufCrm21_1750147040383||'').trim(),expeditorNumber:String(item.ufCrm21_1750147040383||'').trim(),
    city:item.ufCrm_1707397116579||'',addr:item.ufCrm_1707397116579||'',plannedShipment:item.ufCrm21_1751015108375||'',shipmentDate:item.ufCrm21_1753872135589||item.ufCrm21_1751015108375||'',
    contactPerson:item.ufCrm21_1750146663742||'',shippingInfo:item.ufCrm21_1751015048770||'',stage:stageNames[item.stageId]||item.stageId||'',
    bitrixUrl:`${normalizeBitrixWebhook(config.bitrixWebhook).split('/rest/')[0]}/crm/type/1056/details/${item.id}/`,carrierConnected:false,
  }));
  if(config.cdekClientId&&config.cdekClientSecret){
    for(let offset=0;offset<rows.length;offset+=5){
      await Promise.all(rows.slice(offset,offset+5).map(async row=>{if(!row.track)return;try{const status=await fetchCdekOrderStatus(row.track,config);if(status)Object.assign(row,status,{carrierConnected:true});}catch(error){row.cdekError=error.message;}}));
    }
  }
  const data={shipments:rows,total:rows.length,fieldCount:Object.keys(fields).length};
  cdekSamplesCache={expiresAt:Date.now()+10*60*1000,data};
  return data;
}

function parseMegatransRows(html) {
  const rows = [];
  const rowMatches = String(html || '').match(/<tr\b[\s\S]*?<\/tr>/gi) || [];
  for (const rowHtml of rowMatches) {
    const id = (rowHtml.match(/data-id=["']([^"']+)/i) || [])[1] || '';
    const cells = [...rowHtml.matchAll(/<td\b[^>]*>([\s\S]*?)<\/td>/gi)].map(match => stripHtml(match[1]));
    if (cells.length < 8) continue;
    const partyHtml = ([...rowHtml.matchAll(/<td\b[^>]*>([\s\S]*?)<\/td>/gi)][3] || [])[1] || '';
    const parties = [...partyHtml.matchAll(/<(?:div|span)\b[^>]*>([\s\S]*?)<\/(?:div|span)>/gi)].map(match => stripHtml(match[1])).filter(Boolean);
    const [sender = '', recipient = '', payer = ''] = parties.length >= 3 ? parties.slice(0, 3) : cells[3].split(/\s{2,}/);
    const routeParts = cells[2].split(/\s+-\s+/);
    const number = cells[1].split(/\s+/)[0] || id;
    const normalize = value => String(value || '').toLowerCase().replace(/[«»"']/g, '').replace(/\s+/g, ' ').trim();
    const payerType = normalize(payer) === normalize(sender) ? 'our' : (normalize(payer) === normalize(recipient) ? 'client' : 'other');
    const amount = Number(String(cells[5]).replace(/[^\d,.-]/g, '').replace(',', '.')) || 0;
    rows.push({
      id: `megatrans-${id || number}`,
      schet: '', client: recipient, sum: 0, date: '', shipmentDate: cells[0], deliveryDate: '', deliveryDateType: '',
      city: routeParts.slice(1).join(' - ') || cells[2], deliveryStatus: cells[4], stage: '', tk: 'Мегатранс',
      track: number, expeditorNumber: number, payer, payerType,
      payerTypeLabel: payerType === 'our' ? 'Мы платим' : (payerType === 'client' ? 'Клиент платит' : 'Другой плательщик'),
      deliveryCost: amount, tkStatus: cells[4], source: 'megatrans', sender,
      paymentStatus: cells[7], weightVolume: cells[6], route: cells[2]
    });
  }
  return rows;
}

async function fetchMegatransOrders(force = false) {
  if (!force && megatransCache.data && megatransCache.expiresAt > Date.now()) return megatransCache.data;
  const config = loadConfig();
  if (!config.megatransLogin || !config.megatransPassword) throw new Error('Мегатранс не настроен');
  const loginResponse = await fetch('https://lk.megatrans-tk.ru/api/get_login', {
    method: 'POST', headers: { Accept: 'application/json', 'Content-Type': 'application/json; charset=utf-8' },
    body: JSON.stringify({ login: config.megatransLogin, password: config.megatransPassword }), signal: AbortSignal.timeout(30000),
  });
  const loginData = await loginResponse.json();
  if (!loginResponse.ok || loginData.status === 'error') throw new Error(stripHtml(loginData.answer) || 'Не удалось войти в Мегатранс');
  const cookies = typeof loginResponse.headers.getSetCookie === 'function' ? loginResponse.headers.getSetCookie() : [loginResponse.headers.get('set-cookie')].filter(Boolean);
  const cookieJar = new Map();
  for (const item of cookies) {
    const pair = item.split(';')[0];
    const separator = pair.indexOf('=');
    if (separator > 0) cookieJar.set(pair.slice(0, separator), pair.slice(separator + 1));
  }
  const cookie = [...cookieJar].map(([name, value]) => `${name}=${value}`).join('; ');
  const pageResponse = await fetch('https://lk.megatrans-tk.ru/my-orders', { headers: { Cookie: cookie }, signal: AbortSignal.timeout(30000) });
  const page = await pageResponse.text();
  const uid = (page.match(/params\.uid\s*=\s*(\d+)/) || page.match(/params\.uid\s*:\s*(\d+)/) || [])[1];
  if (!uid) throw new Error('Не найден идентификатор кабинета Мегатранс');
  const orderResponse = await fetch('https://lk.megatrans-tk.ru/api/get_orders', {
    method: 'POST', headers: { Accept: 'application/json', 'Content-Type': 'application/json; charset=utf-8', Cookie: cookie },
    body: JSON.stringify({ is_my_company: 1, uid: Number(uid) }), signal: AbortSignal.timeout(60000),
  });
  const orderData = await orderResponse.json();
  if (!orderResponse.ok || !orderData.answer) throw new Error('Мегатранс не вернул список заказов');
  const data = { orders: parseMegatransRows(orderData.answer), total: Number(orderData.total_cnt || 0) };
  megatransCache = { expiresAt: Date.now() + 5 * 60 * 1000, data };
  return data;
}

async function testDellinConnection({ appkey, pat, login, password }) {
  const usePat = Boolean(pat);
  const response = await fetch(usePat ? 'https://api.dellin.ru/v4/auth/login.json' : 'https://api.dellin.ru/v3/auth/login.json', {
    method: 'POST',
    headers: { Accept: 'application/json', 'Content-Type': 'application/json; charset=utf-8' },
    body: JSON.stringify(usePat ? { appkey, pat } : { appkey, login, password }),
    signal: AbortSignal.timeout(30000),
  });
  const data = await response.json().catch(() => ({}));
  const sessionID = data?.data?.sessionID;
  if (!response.ok || !sessionID) {
    const apiMessage = data?.errors?.[0]?.detail || data?.errors?.[0]?.title || data?.error || 'Деловые Линии не подтвердили ключ и PAT';
    throw new Error(stripHtml(apiMessage));
  }
  return { sessionID };
}

function finitePositive(value, name, minimum = 0) {
  const number = Number(value);
  if (!Number.isFinite(number) || number <= minimum) throw new Error(`Некорректное поле: ${name}`);
  return number;
}

function quoteError(carrier, reason, url) {
  return { carrier, available:false, reason, url, sourceLabel:'Нет автоматического расчёта' };
}

async function calculateDellinDelivery(input, config) {
  if (!config.dellinAppKey || (!config.dellinPat && (!config.dellinLogin || !config.dellinPassword))) {
    return quoteError('Деловые Линии','Подключение Деловых Линий не настроено','https://www.dellin.ru/calculator/');
  }
  try {
    const { sessionID } = await testDellinConnection({appkey:config.dellinAppKey,pat:config.dellinPat,login:config.dellinLogin,password:config.dellinPassword});
    const request = {
      appkey:config.dellinAppKey, sessionID,
      delivery:{deliveryType:{type:'auto'},derival:{produceDate:new Date().toISOString().slice(0,10),variant:'address',address:{search:input.from}},arrival:{variant:'address',address:{search:input.to}}},
      cargo:{quantity:input.places,length:input.length,width:input.width,height:input.height,totalVolume:input.volume,totalWeight:input.weight,weight:input.weight,insurance:{statedValue:input.declaredValue,term:Boolean(input.declaredValue)}}
    };
    const response=await fetch('https://api.dellin.ru/v2/calculator.json',{method:'POST',headers:{Accept:'application/json','Content-Type':'application/json; charset=utf-8'},body:JSON.stringify(request),signal:AbortSignal.timeout(35000)});
    const payload=await response.json().catch(()=>({}));
    if(!response.ok || payload.errors?.length){const err=payload.errors?.[0];throw new Error(stripHtml(err?.detail||err?.title||payload.error||`HTTP ${response.status}`));}
    const data=payload.data||payload;
    const price=Number(data.price??data.totalPrice??data.total?.price??data.total?.sum??data.cost??0);
    if(!(price>0)) throw new Error('Калькулятор не вернул итоговую стоимость для указанного маршрута');
    const dates=data.orderDates||data.dates||{};
    const deliveryDate=dates.arrivalToOspReceiver||dates.arrivalToReceiver||dates.arrivalToOspReceiverMax||'';
    let days=Number(data.time?.value||data.deliveryTime||data.days||0);
    if(!days && deliveryDate){const end=new Date(deliveryDate);if(!Number.isNaN(end.getTime()))days=Math.max(1,Math.ceil((end-Date.now())/86400000));}
    return {carrier:'Деловые Линии',available:true,price,days,deliveryDate,sourceLabel:'Официальный API · персональный тариф',details:['Автоперевозка по указанным городам','Страхование учтено'],disclaimer:'Предварительный расчёт Деловых Линий',url:'https://www.dellin.ru/calculator/'};
  } catch(error) { return quoteError('Деловые Линии',error.message,'https://www.dellin.ru/calculator/'); }
}

async function calculateDeliveryQuotes(body) {
  const from=String(body.from||'').trim(); const to=String(body.to||'').trim();
  if(from.length<2||to.length<2) throw new Error('Укажите город отправления и город назначения');
  const places=Math.round(finitePositive(body.places,'Количество мест'));
  const weight=finitePositive(body.weight,'Вес'); const length=finitePositive(body.length,'Длина');
  const width=finitePositive(body.width,'Ширина'); const height=finitePositive(body.height,'Высота');
  const declaredValue=Math.max(0,Number(body.declaredValue||0)); const volume=length*width*height*places;
  const input={from,to,places,weight,length,width,height,volume,declaredValue};
  const config=loadConfig();
  const quotes=await Promise.all([
    calculateDellinDelivery(input,config),
    Promise.resolve(config.baikalApiKey
      ? quoteError('Байкал Сервис','Ключ подключён, но для калькулятора требуется разрешение метода расчёта в API Байкала','https://request.baikalsr.ru/')
      : quoteError('Байкал Сервис','API Байкал Сервис не настроен','https://request.baikalsr.ru/')),
    Promise.resolve(config.megatransLogin
      ? quoteError('Мегатранс','В личном кабинете нет открытого автоматического метода калькулятора','https://megatrans-tk.ru/')
      : quoteError('Мегатранс','Личный кабинет Мегатранс не настроен','https://megatrans-tk.ru/'))
  ]);
  const available=quotes.filter(item=>item.available).sort((a,b)=>a.price-b.price);
  if(available.length){available[0].labels=['Низкая цена'];const fastest=[...available].filter(q=>q.days>0).sort((a,b)=>a.days-b.days)[0];if(fastest){fastest.labels=[...(fastest.labels||[]),'Быстрая доставка'];}if(available.length>1){const optimal=[...available].sort((a,b)=>(a.price/available[0].price)+(a.days||99)/Math.max(1,fastest?.days||99))[0];optimal.labels=[...(optimal.labels||[]),'Оптимально'];}}
  return {calculatedAt:new Date().toISOString(),request:input,quotes};
}

function normalizePartyName(value) {
  return String(value || '').toLowerCase().replace(/[«»"']/g, '').replace(/\s+/g, ' ').trim();
}

function mapDellinOrder(order) {
  const sender = order.sender || {};
  const receiver = order.receiver || {};
  const payer = order.payer || {};
  const dates = order.orderDates || {};
  const payerName = payer.name || '';
  const payerType = payer.inn && sender.inn && payer.inn === sender.inn
    ? 'our'
    : (payer.inn && receiver.inn && payer.inn === receiver.inn
      ? 'client'
      : (normalizePartyName(payerName) === normalizePartyName(sender.name) ? 'our' : (normalizePartyName(payerName) === normalizePartyName(receiver.name) ? 'client' : 'other')));
  const shipmentDate = dates.derivalFromOspSender || dates.pickup || order.produceDate || order.orderedAt || '';
  const actualDelivery = dates.finish || dates.giveoutFromOspReceiver || dates.arrivalToReceiver || '';
  const plannedDelivery = dates.arrivalToOspReceiver || dates.arrivalToOspReceiverMax || order.air?.deliveryDate || '';
  const deliveryDate = actualDelivery || plannedDelivery;
  const cargoPlaces = Array.isArray(order.cargoPlaces) ? order.cargoPlaces.map(item => item.number).filter(Boolean) : [];
  const freight = order.freight || {};
  const orderNumber = String(order.orderId || order.orderNumber || '').trim();
  return {
    id: `dellin-${orderNumber}`,
    schet: order.orderNumber || '',
    client: canonicalCompanyDisplay(receiver.name), clientInn: receiver.inn || '',
    sender: canonicalCompanyDisplay(sender.name), senderInn: sender.inn || '',
    sum: 0, date: '', shipmentDate, deliveryDate,
    deliveryDateType: deliveryDate ? (actualDelivery ? 'Фактическая' : 'Плановая') : '',
    city: order.arrival?.city || order.arrival?.terminalCity || '',
    terminalName: order.arrival?.terminalName || '',
    addr: order.arrival?.terminalAddress || order.arrival?.address || '',
    phone: order.arrival?.terminalPhones || order.arrival?.callCenterPhones || '',
    deliveryStatus: order.stateName || order.state || '', stage: '', tk: 'Деловые Линии',
    track: orderNumber, cargoTracking: cargoPlaces.join(', '), expeditorNumber: orderNumber,
    payer: canonicalCompanyDisplay(payerName), payerType,
    payerTypeLabel: payerType === 'our' ? 'Мы платим' : (payerType === 'client' ? 'Клиент платит' : 'Другой плательщик'),
    weight: Number(freight.weight || 0), volume: Number(freight.volume || 0), places: Number(freight.places || 0),
    weightVolume: `${Number(freight.weight || 0).toLocaleString('ru')} кг / ${Number(freight.volume || 0).toLocaleString('ru', { maximumFractionDigits: 3 })} м³`,
    deliveryCost: Number(order.totalSum || 0), tkStatus: order.stateName || order.state || '',
    paymentStatus: order.isPaid ? 'оплачено' : 'не оплачено',
    route: [order.derival?.city, order.arrival?.city].filter(Boolean).join(' - '),
    contactPerson: receiver.contacts || '', clientPhone: receiver.phones || receiver.anonymPhone || '',
    source: 'dellin'
  };
}

async function fetchDellinOrders(force = false, period = 90) {
  if (!force && period !== 'all' && dellinCache.data && dellinCache.expiresAt > Date.now()) return dellinCache.data;
  const config = loadConfig();
  if (!config.dellinAppKey || (!config.dellinPat && (!config.dellinLogin || !config.dellinPassword))) throw new Error('Деловые Линии не настроены');
  const { sessionID } = await testDellinConnection({
    appkey: config.dellinAppKey, pat: config.dellinPat, login: config.dellinLogin, password: config.dellinPassword
  });
  const rawOrders = [];
  let totalPages = 1;
  const dateTo = new Date();
  const dateFrom = period === 'all' ? new Date(2015, 0, 1) : new Date(dateTo);
  if (period !== 'all') dateFrom.setDate(dateFrom.getDate() - Number(period || 90));
  const dellinDate = (date, end = false) => {
    const year = date.getFullYear();
    const month = String(date.getMonth() + 1).padStart(2, '0');
    const day = String(date.getDate()).padStart(2, '0');
    return `${year}-${month}-${day} ${end ? '23:59:59' : '00:00:00'}`;
  };
  for (let page = 1; page <= totalPages && page <= 1000; page += 1) {
    const response = await fetch('https://api.dellin.ru/v3/orders.json', {
      method: 'POST', headers: { Accept: 'application/json', 'Content-Type': 'application/json; charset=utf-8' },
      body: JSON.stringify({ appkey: config.dellinAppKey, sessionID, page, dateStart: dellinDate(dateFrom), dateEnd: dellinDate(dateTo, true), orderBy: 'ordered_at', orderDatesAdditional: true }),
      signal: AbortSignal.timeout(60000),
    });
    const data = await response.json().catch(() => ({}));
    if (!response.ok || !Array.isArray(data.orders)) {
      const message = data?.errors?.[0]?.detail || data?.errors?.[0]?.title || 'Деловые Линии не вернули журнал заказов';
      throw new Error(stripHtml(message));
    }
    rawOrders.push(...data.orders);
    totalPages = Math.max(1, Number(data?.metadata?.totalPages || 1));
  }
  const orders = rawOrders.map(mapDellinOrder);
  const data = { orders, total: orders.length };
  dellinCache = { expiresAt: Date.now() + 5 * 60 * 1000, data };
  return data;
}

async function fetchBaikalOrders(period) {
  const cacheKey = String(period);
  const cached = baikalCache.get(cacheKey);
  if (cached && cached.expiresAt > Date.now()) return cached.data;
  if (baikalInflight.has(cacheKey)) return baikalInflight.get(cacheKey);
  const request = fetchBaikalOrdersUncached(period, cacheKey, cached);
  baikalInflight.set(cacheKey, request);
  try { return await request; }
  finally { baikalInflight.delete(cacheKey); }
}

async function fetchBaikalOrdersUncached(period, cacheKey, staleCache) {
  const config = loadConfig();
  if (!config.baikalApiKey) throw new Error('Ключ Байкал Сервис не настроен');

  const to = new Date();
  const from = period === 'all' ? new Date(2015, 0, 1) : new Date(to);
  if (period !== 'all') from.setDate(from.getDate() - Number(period));
  const localDate = (date, endOfDay = false) => {
    const year = date.getFullYear();
    const month = String(date.getMonth() + 1).padStart(2, '0');
    const day = String(date.getDate()).padStart(2, '0');
    return `${year}-${month}-${day}T${endOfDay ? '23:59:59' : '00:00:00'}`;
  };
  const auth = Buffer.from(`${config.baikalApiKey}:`).toString('base64');
  const baikalRequestUrl = path => `https://api.baikalsr.ru${path}`;
  const payload = {
    date: { from: localDate(from), to: localDate(to, true) },
    sorting: { date: 'desc' },
    navigation: { page: 0, size: 100 },
  };
  const headers = {
    Authorization: `Basic ${auth}`,
    Accept: 'application/json',
    'Content-Type': 'application/json; charset=utf-8',
  };
  const list = [];
  let recordCount = 0;
  for (let page = 0; page < 1000; page += 1) {
    payload.navigation.page = page;
    let response;
    for (let attempt = 0; attempt < 4; attempt += 1) {
      response = await fetch(baikalRequestUrl('/v2/order/list'), {
        method: 'POST', headers, body: JSON.stringify(payload), signal: AbortSignal.timeout(30000),
      });
      if (response.status !== 429) break;
      if (attempt === 3) {
        if (staleCache?.data) return staleCache.data;
        throw new Error('Байкал Сервис временно ограничил частоту запросов. Повторите обновление через минуту');
      }
      const retryAfter = Number(response.headers.get('retry-after'));
      const waitMs = Number.isFinite(retryAfter) && retryAfter > 0
        ? Math.min(retryAfter * 1000, 15000)
        : 2000 * (attempt + 1);
      await new Promise(resolve => setTimeout(resolve, waitMs));
    }
    if (!response.ok) throw new Error(`Байкал Сервис вернул HTTP ${response.status}`);
    const pageData = await response.json();
    if (pageData.error || pageData.errors) throw new Error(pageData.error || 'Ошибка API Байкал Сервис');
    const pageList = Array.isArray(pageData.orderList) ? pageData.orderList : [];
    recordCount = Number(pageData.recordCount || pageList.length);
    list.push(...pageList);
    if (!pageList.length || list.length >= recordCount) break;
    // Baikal limits bursts even for valid keys. One paced request stream also
    // prevents several open dashboard tabs from multiplying the API traffic.
    await new Promise(resolve => setTimeout(resolve, 800));
  }
  const detailsList = period === 'all' ? list.slice(0, 100) : list;
  let rateLimited = false;
  for (let offset = 0; offset < detailsList.length && !rateLimited; offset += 2) {
    const batch = detailsList.slice(offset, offset + 2);
    await Promise.all(batch.map(async (order) => {
      if (baikalDetailCache.has(order.number)) {
        order.detail = baikalDetailCache.get(order.number);
        return;
      }
      try {
        const detailResponse = await fetch(baikalRequestUrl('/v2/order/detail'), {
          method: 'POST',
          headers,
          body: JSON.stringify({ number: order.number }),
          signal: AbortSignal.timeout(30000),
        });
        if (detailResponse.status === 429) {
          rateLimited = true;
          return;
        }
        const detail = await detailResponse.json();
        if (detailResponse.ok && !detail.error && !detail.errors) {
          order.detail = detail;
          baikalDetailCache.set(order.number, detail);
        }
      } catch (_) {
        order.detail = null;
      }
    }));
  }
  const data = { recordCount, orderList: list };
  baikalCache.set(cacheKey, { expiresAt: Date.now() + 5 * 60 * 1000, data });
  return data;
}

function serveFile(req, res) {
  const requestPath = req.url === '/' ? '/index.html' : req.url.split('?')[0];
  const resolved = path.resolve(PUBLIC_ROOT, `.${requestPath}`);
  if (!resolved.startsWith(`${path.resolve(PUBLIC_ROOT)}${path.sep}`)) {
    res.writeHead(403); res.end('Forbidden'); return;
  }
  fs.readFile(resolved, (error, content) => {
    if (error) { res.writeHead(error.code === 'ENOENT' ? 404 : 500); res.end('Not found'); return; }
    const ext = path.extname(resolved).toLowerCase();
    const types = { '.html': 'text/html; charset=utf-8', '.css': 'text/css; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.jpg': 'image/jpeg', '.png': 'image/png' };
    res.writeHead(200, { 'Content-Type': types[ext] || 'application/octet-stream', 'Cache-Control': 'no-store' });
    res.end(content);
  });
}

const server = http.createServer(async (req, res) => {
  const cleanUrl = req.url.split('?')[0];
  if (req.method === 'POST' && cleanUrl === '/api/auth/login') {
    try {
      const body = await readBody(req);
      const user = configuredAuthUsers().find(item => safeEqual(String(item.username || '').toLowerCase(), String(body.username || '').trim().toLowerCase()));
      if (!user || !verifyPassword(body.password, user)) return json(res, 401, { error: 'Неверный логин или пароль' });
      const token = crypto.randomBytes(32).toString('hex');
      const session = { username:user.username, role:user.role || 'employee', expiresAt:Date.now() + AUTH_SESSION_TTL };
      authSessions.set(token, session);
      res.setHeader('Set-Cookie', `akfix_session=${token}; Path=/; HttpOnly; SameSite=Strict; Max-Age=${Math.floor(AUTH_SESSION_TTL / 1000)}`);
      return json(res, 200, { username:session.username, role:session.role, expiresAt:session.expiresAt });
    } catch(error) { return json(res, 400, { error:error.message }); }
  }
  if (req.method === 'GET' && cleanUrl === '/api/auth/me') {
    const users = configuredAuthUsers();
    if (!users.length) return json(res, 200, { configured:false });
    const session = sessionForRequest(req);
    return session ? json(res, 200, { configured:true, authenticated:true, username:session.username, role:session.role, expiresAt:session.expiresAt }) : json(res, 200, { configured:true, authenticated:false });
  }
  if (req.method === 'POST' && cleanUrl === '/api/auth/logout') {
    const token = parseCookies(req).akfix_session;
    if (token) authSessions.delete(token);
    res.setHeader('Set-Cookie', 'akfix_session=; Path=/; HttpOnly; SameSite=Strict; Max-Age=0');
    return json(res, 200, { ok:true });
  }
  if (!cleanUrl.startsWith('/api/')) return serveFile(req, res);
  if (!authorizeRequest(req, res)) return;
  if (req.method === 'POST' && cleanUrl === '/api/warehouse-dashboard/bitrix') {
    try {
      const body = await readBody(req);
      const method = String(body.method || '');
      if (method === 'warehouse.invoice.stats') {
        const config = loadConfig();
        if (!config.bitrixWebhook) throw new Error('Bitrix24 не настроен');
        const items = await invoiceStatsForItems(config.bitrixWebhook, body.params?.items);
        return json(res, 200, { result:{ items } });
      }
      const allowedMethods = new Set([
        'profile',
        'crm.item.fields',
        'crm.status.list',
        'crm.item.list',
        'crm.company.list',
        'crm.contact.list',
        'user.get',
        'crm.stagehistory.list',
      ]);
      if (!allowedMethods.has(method)) return json(res, 403, { error:'Метод Bitrix24 не разрешён для дашборда' });
      const config = loadConfig();
      if (!config.bitrixWebhook) throw new Error('Bitrix24 не настроен');
      const result = await bitrixCall(config.bitrixWebhook, method, body.params && typeof body.params === 'object' ? body.params : {});
      return json(res, 200, sanitizeWarehouseDashboardPayload(result));
    } catch (error) {
      return json(res, 502, { error:error.message });
    }
  }
  if (req.method === 'POST' && cleanUrl === '/api/system/refresh') {
    if (req.auth?.role !== 'admin') return json(res,403,{error:'Принудительное обновление доступно только администратору'});
    const started=!refreshWorker;
    startSnapshotRefreshWorker();
    return json(res,202,{ok:true,started,intervalMinutes:15});
  }
  if (req.method === 'GET' && req.url.startsWith('/api/bitrix-photo')) {
    try {
      const url = new URL(req.url, `http://${HOST}:${PORT}`);
      const itemId = Number(url.searchParams.get('itemId'));
      const fileId = Number(url.searchParams.get('fileId'));
      const fieldName = String(url.searchParams.get('fieldName') || '');
      if (!Number.isFinite(itemId) || !Number.isFinite(fileId) || !BITRIX_PHOTO_FIELDS.includes(fieldName)) throw new Error('Некорректная ссылка фотографии');
      const config = loadConfig();
      const item = await bitrixPhotoItem(config.bitrixWebhook, itemId);
      const value = item[fieldName];
      const files = Array.isArray(value) ? value : (value ? [value] : []);
      const file = files.find(entry => Number(entry?.id || entry) === fileId);
      if (!file?.urlMachine) throw new Error('Фотография не найдена');
      const photoResponse = await fetchBitrixPhoto(file.urlMachine);
      const content = Buffer.from(await photoResponse.arrayBuffer());
      res.writeHead(200, {
        'Content-Type': photoResponse.headers.get('content-type') || 'image/jpeg',
        'Content-Length': content.length,
        'Cache-Control': 'private, max-age=3600',
        'X-Content-Type-Options': 'nosniff',
      });
      res.end(content);
    } catch(error) { json(res,404,{error:error.message}); }
    return;
  }
  if (req.method === 'GET' && req.url.startsWith('/api/bitrix-invoice')) {
    try {
      const url = new URL(req.url, `http://${HOST}:${PORT}`);
      const itemId = Number(url.searchParams.get('itemId'));
      const fileId = Number(url.searchParams.get('fileId'));
      if (!Number.isFinite(itemId) || !Number.isFinite(fileId)) throw new Error('Некорректная ссылка счёта');
      const config = loadConfig();
      const item = await bitrixPhotoItem(config.bitrixWebhook, itemId);
      const value = item[BITRIX_INVOICE_FIELD];
      const files = Array.isArray(value) ? value : (value ? [value] : []);
      const file = files.find(entry => Number(entry?.id || entry) === fileId);
      if (!file?.urlMachine) throw new Error('Счёт не найден');
      const invoiceResponse = await fetchBitrixPhoto(file.urlMachine);
      const content = Buffer.from(await invoiceResponse.arrayBuffer());
      res.writeHead(200, {
        'Content-Type': 'application/pdf',
        'Content-Length': content.length,
        'Content-Disposition': `inline; filename="invoice-${fileId}.pdf"`,
        'Cache-Control': 'private, max-age=86400',
        'X-Content-Type-Options': 'nosniff',
      });
      res.end(content);
    } catch(error) { json(res,404,{error:error.message}); }
    return;
  }
  if (req.method === 'GET' && req.url === '/api/dashboard-snapshot') {
    try {
      if(!fs.existsSync(DASHBOARD_SNAPSHOT_FILE)) return json(res,404,{error:'Снимок ещё не создан'});
      const snapshot=JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE,'utf8'));
      // CDEK can be mentioned in Bitrix delivery details/address instead of
      // the dedicated carrier field. Derive these rows from the last good
      // server snapshot so employees still see them while carrier APIs are
      // temporarily unavailable.
      const cdekMain=(snapshot.orders||[])
        .filter(item=>item.bitrixId&&isCdekOrder(item))
        .map(item=>({...item,tk:'СДЭК',carrierHint:'СДЭК',sourceType:'Отгрузки'}));
      const cdekSamples=(snapshot.cdekShipments||[]).filter(item=>item.sourceType==='Отправка образцов');
      const cdekUnique=new Map();
      [...cdekMain,...cdekSamples].forEach(item=>cdekUnique.set(String(item.bitrixId||item.uuid||item.schet||Math.random()),item));
      snapshot.cdekShipments=[...cdekUnique.values()];
      json(res,200,snapshot);
    } catch(error) { json(res,500,{error:error.message}); }
    return;
  }
  if (req.method === 'GET' && req.url === '/api/integration-status') {
    try {
      const config=loadConfig();
      let archive={rows:[],savedAt:null,full:false};
      try { if(fs.existsSync(CARRIER_ARCHIVE_FILE)) archive=JSON.parse(fs.readFileSync(CARRIER_ARCHIVE_FILE,'utf8')); } catch(_) {}
      json(res,200,{bitrix:Boolean(config.bitrixWebhook),baikal:Boolean(config.baikalApiKey),dellin:Boolean(config.dellinAppKey&&(config.dellinPat||(config.dellinLogin&&config.dellinPassword))),megatrans:Boolean(config.megatransLogin&&config.megatransPassword),cdek:Boolean(config.cdekClientId&&config.cdekClientSecret),archive:{count:(archive.rows||[]).length,savedAt:archive.savedAt,full:Boolean(archive.full)}});
    } catch(error) { json(res,500,{error:error.message}); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/dashboard-snapshot') {
    json(res,403,{error:'Общий снимок обновляется только сервером'});
    return;
  }
  if (req.method === 'GET' && req.url.startsWith('/api/google-logistics')) {
    try { json(res, 200, await fetchGoogleLogistics(req.url.includes('force=1'))); }
    catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/export/xlsx') {
    try {
      const body = await readBody(req);
      const buffer = await buildLogisticsWorkbook(body);
      const stamp = new Date().toISOString().slice(0, 10);
      res.writeHead(200, {
        'Content-Type': 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
        'Content-Disposition': `attachment; filename="akfix_logistics_${stamp}.xlsx"`,
        'Content-Length': buffer.length,
        'Cache-Control': 'no-store',
        'X-Content-Type-Options': 'nosniff',
      });
      res.end(Buffer.from(buffer));
    } catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/bitrix/config') {
    try {
      const body = await readBody(req);
      const webhook = normalizeBitrixWebhook(body.webhook);
      const checked = await testBitrixConnection(webhook);
      saveConfig({ bitrixWebhook: webhook });
      bitrixCache = { expiresAt: 0, data: null };
      const data = await fetchBitrixOrders(true);
      json(res, 200, { ok: true, userId: checked.profile.ID, count: data.total, startStage: data.startStage, stages: data.stages });
    } catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'GET' && req.url.startsWith('/api/bitrix/orders')) {
    try { json(res, 200, await fetchBitrixOrders()); }
    catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'GET' && req.url === '/api/manual-matches') {
    const config = loadConfig();
    json(res, 200, { matches: config.manualShipmentMatches || {} });
    return;
  }
  if (req.method === 'POST' && req.url === '/api/manual-matches') {
    try {
      const body = await readBody(req);
      const schet = String(body.schet || '').trim();
      const expeditor = String(body.expeditor || '').trim();
      const carrier = String(body.carrier || '').trim();
      if(!schet || !expeditor) throw new Error('Укажите счёт и экспедиторскую расписку');
      if(!['Байкал Сервис','Деловые Линии','Мегатранс'].includes(carrier)) throw new Error('Можно сопоставлять только подключённые ТК');
      const config = loadConfig();
      const matches = { ...(config.manualShipmentMatches || {}), [schet]: { expeditor, carrier, updatedAt:new Date().toISOString() } };
      const learned = learnCounterpartiesFromManualMatches(config, [{ schet, expeditor, carrier }]);
      saveConfig({ manualShipmentMatches:matches, counterparties:learned.counterparties });
      const resolved = applyManualMatchesToSavedSnapshot([{ schet, expeditor, carrier }]);
      // Run expensive carrier/Bitrix synchronization in the dedicated worker.
      // Keeping it out of the HTTP process prevents the UI from freezing after
      // a manual match is saved.
      setTimeout(startSnapshotRefreshWorker, 50);
      json(res, 200, { ok:true, match:matches[schet], resolved, learnedCounterparties:learned.learned });
    } catch(error) { json(res, 400, { error:error.message }); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/manual-matches/bulk') {
    try {
      const body = await readBody(req);
      const rows = Array.isArray(body.rows) ? body.rows : [];
      if(!rows.length) throw new Error('Нет строк для сохранения');
      if(rows.length > 5000) throw new Error('За один раз можно сохранить не более 5000 строк');
      const allowed = new Set(['Байкал Сервис','Деловые Линии','Мегатранс']);
      const config = loadConfig();
      const matches = { ...(config.manualShipmentMatches || {}) };
      let saved = 0;
      const errors = [];
      for (const [index,row] of rows.entries()) {
        const schet = String(row?.schet || '').trim();
        const expeditor = String(row?.expeditor || '').trim();
        const carrier = String(row?.carrier || '').trim();
        if(!schet || !expeditor || !allowed.has(carrier)) { errors.push(index + 1); continue; }
        matches[schet] = { expeditor, carrier, updatedAt:new Date().toISOString() };
        saved += 1;
      }
      if(!saved) throw new Error('Не удалось распознать счёт, расписку и транспортную компанию');
      const validRows = rows.filter(row => row?.schet && row?.expeditor && allowed.has(String(row?.carrier || '').trim()));
      const learned = learnCounterpartiesFromManualMatches(config, validRows);
      saveConfig({ manualShipmentMatches:matches, counterparties:learned.counterparties });
      const resolved = applyManualMatchesToSavedSnapshot(validRows);
      setTimeout(startSnapshotRefreshWorker, 50);
      json(res, 200, { ok:true, saved, resolved, learnedCounterparties:learned.learned, skipped:errors.length, skippedRows:errors.slice(0,20) });
    } catch(error) { json(res, 400, { error:error.message }); }
    return;
  }
  if (req.method === 'GET' && req.url === '/api/counterparties') {
    const config = loadConfig();
    json(res, 200, { counterparties: config.counterparties || [] });
    return;
  }
  if (req.method === 'GET' && req.url.startsWith('/api/counterparty-suggestions')) {
    try {
      const url = new URL(req.url, `http://${HOST}:${PORT}`);
      const id = url.searchParams.get('id');
      const config = loadConfig();
      const counterparty = (config.counterparties || []).find(item => item.id === id);
      if (!counterparty) throw new Error('Контрагент не найден');
      const snapshot = fs.existsSync(DASHBOARD_SNAPSHOT_FILE) ? JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE, 'utf8')) : { unmatchedMatchOrders:[] };
      const archive = fs.existsSync(CARRIER_ARCHIVE_FILE) ? JSON.parse(fs.readFileSync(CARRIER_ARCHIVE_FILE, 'utf8')) : { rows:[] };
      const variants = [counterparty.name, ...(counterparty.aliases || []), ...(counterparty.contacts || [])].map(normalizeMatchText).filter(Boolean);
      const belongs = value => {
        const normalized = normalizeMatchText(value);
        return Boolean(normalized && variants.some(candidate => candidate === normalized || (candidate.length >= 5 && (candidate.includes(normalized) || normalized.includes(candidate)))));
      };
      const family = value => {
        const normalized = normalizeMatchText(value);
        if (/байкал/.test(normalized)) return 'baikal';
        if (/делов/.test(normalized)) return 'dellin';
        if (/мега\s*транс|мегатранс/.test(normalized)) return 'megatrans';
        return '';
      };
      const carrierName = value => ({baikal:'Байкал Сервис',dellin:'Деловые Линии',megatrans:'Мегатранс'}[family(value)] || String(value || ''));
      const carrierRows = consolidateCarrierShipments(archive.rows || []).filter(row => belongs(row.client));
      const suggestions = [];
      const suggestedShipments = new Set();
      const shipmentKey = carrier => [carrier.source, carrier.expeditorNumber, carrier.track, carrier.cargoTracking]
        .map(value => String(value || '').replace(/\s+/g,'').toLowerCase()).join('|');
      for (const order of snapshot.unmatchedMatchOrders || []) {
        if (!belongs(order.client) && !belongs(order.contactPerson) && !belongs(order.shippingInfo)) continue;
        const orderFamily = family(order.carrierHint || order.tk);
        if (!orderFamily) continue;
        const orderDate = matchDate(order.shipmentDate || order.date);
        const orderCity = cleanMatchCity(order.city || order.addr);
        const candidates = carrierRows.map(carrier => {
          if (suggestedShipments.has(shipmentKey(carrier))) return null;
          if (family(carrier.tk) !== orderFamily) return null;
          const shipmentDate = matchDate(carrier.shipmentDate || carrier.date);
          const days = orderDate && shipmentDate ? Math.abs(orderDate - shipmentDate) / 86400000 : null;
          if (days === null || days > 3) return null;
          const city = cleanMatchCity(carrier.city || carrier.addr);
          const cityMatch = Boolean(orderCity && city && (orderCity.includes(city) || city.includes(orderCity)));
          let score = 75 + (days <= 1 ? 20 : 10) + (cityMatch ? 15 : 0);
          return { carrier, score, days, cityMatch };
        }).filter(Boolean).sort((a,b)=>b.score-a.score);
        if (!candidates.length) continue;
        const best = candidates[0];
        const second = candidates[1];
        suggestedShipments.add(shipmentKey(best.carrier));
        suggestions.push({
          schet:order.schet, orderClient:order.client, orderCity:order.city || order.addr || '',
          orderDate:order.shipmentDate || order.date || '', carrier:carrierName(best.carrier.tk),
          carrierClient:best.carrier.client || '', carrierCity:best.carrier.city || '',
          expeditor:best.carrier.expeditorNumber || best.carrier.track || best.carrier.cargoTracking || '',
          cargoTracking:best.carrier.cargoTracking || '', deliveryCost:Number(best.carrier.deliveryCost || 0),
          confidence:Math.min(99, best.score), alternatives:candidates.length,
          ambiguous:Boolean(second && best.score - second.score < 10)
        });
      }
      json(res, 200, { id, name:counterparty.name, suggestions });
    } catch(error) { json(res, 400, { error:error.message }); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/counterparties') {
    try {
      if (req.auth && !['admin','logist'].includes(req.auth.role)) throw new Error('Изменять справочник может логист или администратор');
      const body = await readBody(req);
      const name = String(body.name || '').trim();
      const inn = String(body.inn || '').replace(/\D/g, '');
      const cleanList = value => [...new Set((Array.isArray(value) ? value : []).map(item => String(item || '').trim()).filter(Boolean))].slice(0,100);
      if (!name) throw new Error('Укажите основное название контрагента');
      if (inn && ![10,12].includes(inn.length)) throw new Error('ИНН должен содержать 10 или 12 цифр');
      const config = loadConfig();
      const counterparties = [...(config.counterparties || [])];
      const existingIndex = counterparties.findIndex(item => normalizeMatchText(item.name) === normalizeMatchText(name) || (inn && item.inn === inn));
      const existing = existingIndex >= 0 ? counterparties[existingIndex] : null;
      const item = {
        id: existing?.id || crypto.randomUUID(), name, inn,
        aliases: cleanList([...(existing?.aliases || []), ...cleanList(body.aliases)]),
        contacts: cleanList([...(existing?.contacts || []), ...cleanList(body.contacts)]),
        phones: cleanList([...(existing?.phones || []), ...cleanList(body.phones)]),
        updatedAt: new Date().toISOString()
      };
      if (existingIndex >= 0) counterparties[existingIndex] = item; else counterparties.unshift(item);
      saveConfig({ counterparties });
      setTimeout(startSnapshotRefreshWorker, 50);
      json(res, 200, { ok:true, counterparty:item, counterparties });
    } catch(error) { json(res, 400, { error:error.message }); }
    return;
  }
  if (req.method === 'DELETE' && req.url.startsWith('/api/counterparties/')) {
    try {
      if (req.auth && !['admin','logist'].includes(req.auth.role)) throw new Error('Изменять справочник может логист или администратор');
      const id = decodeURIComponent(req.url.slice('/api/counterparties/'.length));
      const config = loadConfig();
      const counterparties = (config.counterparties || []).filter(item => item.id !== id);
      saveConfig({ counterparties });
      json(res, 200, { ok:true, counterparties });
    } catch(error) { json(res, 400, { error:error.message }); }
    return;
  }
  if (req.method === 'GET' && req.url === '/api/custom-carriers') {
    const config = loadConfig();
    const configured = config.customCarriers || [];
    let snapshot = { orders: [] };
    try { if (fs.existsSync(DASHBOARD_SNAPSHOT_FILE)) snapshot = JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE, 'utf8')); } catch (_) {}
    const counts = new Map();
    const carrierSourceOrders=(snapshot.orders||[]).length ? snapshot.orders : (bitrixCache.data?.orders||[]);
    for (const order of carrierSourceOrders) {
      if (!order.bitrixId || order.carrierConnected !== false) continue;
      const name = String(order.carrierHint || order.tk || '').trim();
      if (!name || /^(тк\s+не\s+указана|байкал сервис|деловые линии|мегатранс)$/i.test(name)) continue;
      const canonicalName = resolveCarrierAlias(name, config);
      const groupKey = normalizeCarrierKey(canonicalName) || normalizeMatchText(canonicalName);
      const current = counts.get(groupKey) || { name:canonicalName, sources:new Set(), orderCount:0 };
      current.sources.add(name);
      current.orderCount += 1;
      counts.set(groupKey, current);
    }
    const configuredNames = new Set(configured.map(item => normalizeCarrierKey(item.name)));
    const detected = [...counts.entries()].filter(([groupKey]) => !configuredNames.has(groupKey))
      .sort((a, b) => b[1].orderCount - a[1].orderCount).map(([groupKey,item]) => ({
        id:`detected-${crypto.createHash('sha1').update(groupKey).digest('hex').slice(0,10)}`,
        name:item.name, canonicalName:item.name, sourceNames:[...item.sources], orderCount:item.orderCount,
        detected:true, mode:'manual', status:'Без API'
      }));
    json(res, 200, { carriers: [...configured, ...detected] });
    return;
  }
  if (req.method === 'POST' && req.url === '/api/carrier-aliases') {
    try {
      const body = await readBody(req);
      const sourceName = String(body.sourceName || '').trim();
      const canonicalName = String(body.canonicalName || '').trim();
      if (!sourceName || !canonicalName) throw new Error('Укажите исходное и правильное название ТК');
      const config = loadConfig();
      const aliases = { ...(config.carrierAliases || {}), [normalizeMatchText(sourceName)]: canonicalName };
      const sourceKey = normalizeCarrierKey(sourceName);
      let snapshot = { orders:[] };
      try { if (fs.existsSync(DASHBOARD_SNAPSHOT_FILE)) snapshot=JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE,'utf8')); } catch (_) {}
      for (const order of snapshot.orders || []) {
        const candidate=String(order.carrierHint||order.tk||'').trim();
        if(candidate && normalizeCarrierKey(candidate) === sourceKey) aliases[normalizeMatchText(candidate)] = canonicalName;
      }
      saveConfig({ carrierAliases: aliases });
      // Apply the rename immediately to the prepared server snapshot. Users
      // should not have to wait for the next 15-minute Bitrix refresh.
      const renameRows=rows=>(rows||[]).map(row=>{
        const tk=String(row.tk||'').trim();
        const hint=String(row.carrierHint||'').trim();
        const matches=[tk,hint].some(value=>value&&normalizeCarrierKey(value)===sourceKey);
        return matches?{...row,tk:canonicalName,carrierHint:canonicalName}:row;
      });
      snapshot={...snapshot,
        orders:renameRows(snapshot.orders),
        ourDeliveries:renameRows(snapshot.ourDeliveries),
        selfPickups:renameRows(snapshot.selfPickups),
        unmatchedMatchOrders:renameRows(snapshot.unmatchedMatchOrders),
        cdekShipments:renameRows(snapshot.cdekShipments),
      };
      writeDashboardSnapshot(snapshot);
      setTimeout(startSnapshotRefreshWorker, 50);
      json(res, 200, { ok:true, sourceName, canonicalName });
    } catch (error) { json(res, 400, { error:error.message }); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/carrier-aliases/bulk') {
    try {
      const body=await readBody(req);
      const rows=(Array.isArray(body.rows)?body.rows:[]).slice(0,5000).map(row=>({
        sourceName:String(row.sourceName||'').trim(), canonicalName:String(row.canonicalName||'').trim()
      })).filter(row=>row.sourceName&&row.canonicalName);
      if(!rows.length) throw new Error('Нет названий для применения');
      const config=loadConfig();
      const aliases={...(config.carrierAliases||{})};
      const rules=rows.map(row=>({...row,sourceKey:normalizeCarrierKey(row.sourceName)}));
      for(const rule of rules) aliases[normalizeMatchText(rule.sourceName)]=rule.canonicalName;
      let snapshot={orders:[]};
      try { if(fs.existsSync(DASHBOARD_SNAPSHOT_FILE)) snapshot=JSON.parse(fs.readFileSync(DASHBOARD_SNAPSHOT_FILE,'utf8')); } catch(_) {}
      const collections=['orders','ourDeliveries','selfPickups','unmatchedMatchOrders','cdekShipments'];
      for(const key of collections) for(const row of snapshot[key]||[]) {
        for(const value of [row.tk,row.carrierHint]) {
          const candidate=String(value||'').trim();
          const rule=rules.find(item=>candidate&&normalizeCarrierKey(candidate)===item.sourceKey);
          if(rule) aliases[normalizeMatchText(candidate)]=rule.canonicalName;
        }
      }
      saveConfig({carrierAliases:aliases});
      let updatedOrders=0;
      const renameRows=(items,isMain=false)=>(items||[]).map(row=>{
        const values=[row.tk,row.carrierHint].map(value=>String(value||'').trim()).filter(Boolean);
        const rule=rules.find(item=>values.some(value=>normalizeCarrierKey(value)===item.sourceKey));
        if(!rule)return row;
        if(isMain)updatedOrders++;
        return {...row,tk:rule.canonicalName,carrierHint:rule.canonicalName};
      });
      snapshot={...snapshot,
        orders:renameRows(snapshot.orders,true),
        ourDeliveries:renameRows(snapshot.ourDeliveries),
        selfPickups:renameRows(snapshot.selfPickups),
        unmatchedMatchOrders:renameRows(snapshot.unmatchedMatchOrders),
        cdekShipments:renameRows(snapshot.cdekShipments)
      };
      writeDashboardSnapshot(snapshot);
      setTimeout(startSnapshotRefreshWorker,50);
      json(res,200,{ok:true,saved:rules.length,updatedOrders});
    } catch(error) { json(res,400,{error:error.message}); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/custom-carriers') {
    try {
      const body=await readBody(req);
      const name=String(body.name||'').trim();
      const cabinetUrl=String(body.cabinetUrl||'').trim();
      const mode=body.mode === 'cabinet' ? 'cabinet' : 'manual';
      if(!name) throw new Error('Укажите название ТК');
      if(cabinetUrl && !/^https:\/\//i.test(cabinetUrl)) throw new Error('Ссылка на личный кабинет должна начинаться с https://');
      const config=loadConfig();
      const carriers=[...(config.customCarriers||[])];
      const item={id:crypto.randomUUID(),name,cabinetUrl,mode,status:mode==='cabinet'?'Требуется настройка':'Ручное сопоставление'};
      carriers.push(item); saveConfig({customCarriers:carriers});
      json(res,200,{ok:true,carrier:item,carriers});
    } catch(error) { json(res,400,{error:error.message}); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/dellin/config') {
    try {
      const body = await readBody(req);
      const appkey = String(body.appkey || '').trim();
      const pat = String(body.pat || '').trim();
      const loginRaw = String(body.login || '').trim();
      const loginDigits = loginRaw.replace(/\D/g, '');
      const login = loginDigits.length === 11
        ? `+7${loginDigits.slice(1)}`
        : (loginDigits.length === 10 ? `+7${loginDigits}` : loginRaw);
      const password = String(body.password || '');
      if (!appkey) throw new Error('Укажите API-ключ Деловых Линий');
      if (!pat && (!login || !password)) throw new Error('Укажите PAT либо телефон и пароль личного кабинета');
      await testDellinConnection({ appkey, pat, login, password });
      saveConfig({ dellinAppKey: appkey, dellinPat: pat, dellinLogin: pat ? '' : login, dellinPassword: pat ? '' : password });
      dellinCache = { expiresAt: 0, data: null };
      const data = await fetchDellinOrders(true);
      json(res, 200, { ok: true, mode: pat ? 'pat' : 'password', count: data.orders.length });
    } catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/cdek/config') {
    try {
      const body=await readBody(req);
      const clientId=String(body.clientId||'').trim();
      const clientSecret=String(body.clientSecret||'').trim();
      if(!clientId||!clientSecret) throw new Error('Укажите идентификатор и секретный ключ СДЭК');
      // Persist first. A temporary DNS/firewall failure must not erase valid
      // credentials entered by the administrator.
      saveConfig({cdekClientId:clientId,cdekClientSecret:clientSecret});
      cdekTokenCache={expiresAt:0,token:''};
      let verified=true;
      let warning='';
      try { await getCdekToken({cdekClientId:clientId,cdekClientSecret:clientSecret}); }
      catch(error) {
        verified=false;
        warning=/fetch failed|timeout|enotfound|econn/i.test(`${error.message} ${error.cause?.code||''}`)
          ? 'Ключи сохранены. Сервер временно не смог связаться со СДЭК и проверит их при следующем фоновом обновлении.'
          : `Ключи сохранены, но СДЭК не подтвердил подключение: ${error.message}`;
      }
      cdekSamplesCache={expiresAt:0,data:null};
      setTimeout(refreshDashboardSnapshotInBackground,50);
      json(res,200,{ok:true,verified,warning});
    } catch(error) { json(res,400,{error:error.message}); }
    return;
  }
  if (req.method === 'GET' && req.url === '/api/cdek/shipments') {
    try { json(res,200,await fetchBitrixCdekSamples()); }
    catch(error) { json(res,400,{error:error.message}); }
    return;
  }
  if (req.method === 'GET' && req.url.startsWith('/api/dellin/orders')) {
    try { json(res, 200, await fetchDellinOrders()); }
    catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/megatrans/config') {
    try {
      const body = await readBody(req);
      if (!body.login || !body.password) throw new Error('Укажите логин и пароль Мегатранс');
      saveConfig({ megatransLogin: String(body.login).trim(), megatransPassword: String(body.password) });
      megatransCache = { expiresAt: 0, data: null };
      const data = await fetchMegatransOrders(true);
      json(res, 200, { ok: true, count: data.orders.length });
    } catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'GET' && req.url.startsWith('/api/megatrans/orders')) {
    try { json(res, 200, await fetchMegatransOrders()); }
    catch (error) { json(res, 400, { error: error.message }); }
    return;
  }
  if (req.method === 'GET' && req.url.startsWith('/api/baikal/orders')) {
    try {
      const url = new URL(req.url, `http://${HOST}:${PORT}`);
      const requested = url.searchParams.get('period') || url.searchParams.get('days') || '30';
      const period = requested === 'all' ? 'all' : Math.min(3650, Math.max(1, Number(requested) || 30));
      const data = await fetchBaikalOrders(period);
      json(res, 200, data);
    } catch (error) {
      json(res, 502, { error: error.message });
    }
    return;
  }
  if (req.method === 'POST' && req.url === '/api/delivery-calculator') {
    try { json(res,200,await calculateDeliveryQuotes(await readBody(req))); }
    catch(error) { json(res,400,{error:error.message}); }
    return;
  }
  if (req.method !== 'GET') { res.writeHead(405); res.end('Method not allowed'); return; }
  serveFile(req, res);
});

server.on('error', (error) => {
  if (error.code === 'EADDRINUSE') {
    console.log(`Akfix Logistics уже запущен: http://${HOST}:${PORT}`);
    process.exit(0);
  }
  console.error('Не удалось запустить Akfix Logistics:', error.message);
  process.exit(1);
});

if (process.env.AKFIX_REFRESH_ONCE === '1') {
  const refreshTask=process.env.AKFIX_REFRESH_MODE==='bitrix'?refreshBitrixSnapshotQuick:refreshDashboardSnapshotInBackground;
  refreshTask().then(() => process.exit(0)).catch(error => {
    console.error('[snapshot] Ошибка рабочего процесса:', error.message);
    process.exit(1);
  });
} else {
  const savedManual = loadConfig().manualShipmentMatches || {};
  applyManualMatchesToSavedSnapshot(Object.entries(savedManual).map(([schet, value]) => ({ schet, ...value })));
  server.listen(PORT, HOST, () => {
    console.log(`Akfix Logistics: http://${HOST}:${PORT}`);
    console.log('Для остановки нажмите Ctrl+C');
    setTimeout(()=>startSnapshotRefreshWorker('bitrix'),5*1000);
    setInterval(()=>startSnapshotRefreshWorker('bitrix'),60*1000);
    setTimeout(()=>startSnapshotRefreshWorker('full'),2*60*1000);
    setInterval(()=>startSnapshotRefreshWorker('full'),10*60*1000);
    console.log('Bitrix24: каждую минуту; таблица отгрузок, транспортные компании и полное сопоставление: каждые 10 минут');
  });
}
