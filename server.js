const express = require('express');
const http = require('http');
const path = require('path');
const fs = require('fs');
const os = require('os');
const tls = require('tls');
const crypto = require('crypto');
const { Server } = require('socket.io');

const app = express();

const DEFAULT_ALLOWED_ORIGINS = [
  'https://wildsnake.onrender.com',
  'http://localhost:3000',
  'http://127.0.0.1:3000',
  /* Capacitor Android/iOS local WebView origins. */
  'https://localhost',
  'http://localhost',
  'capacitor://localhost'
];

const ALLOWED_ORIGINS = new Set([
  ...DEFAULT_ALLOWED_ORIGINS,
  ...String(process.env.ALLOWED_ORIGINS || '')
    .split(',')
    .map(value => value.trim())
    .filter(Boolean)
]);

function originAllowed(origin) {
  if (!origin) return true; // apps nativos, curl e handshake sem Origin
  return ALLOWED_ORIGINS.has(origin);
}

app.disable('x-powered-by');
app.set('trust proxy', 1);

/* =========================================================
   v13.25 - CORS DO APP NATIVO + CROSSPLAY (CAPACITOR)
   Permite apenas origens explicitamente aprovadas acima.
   O app continua usando o MESMO backend/Socket.IO do navegador.
========================================================= */
app.use((req, res, next) => {
  const origin = String(req.headers.origin || '').trim();

  if (origin && originAllowed(origin)) {
    res.set('Access-Control-Allow-Origin', origin);
    res.set('Vary', 'Origin');
    res.set('Access-Control-Allow-Methods', 'GET,POST,OPTIONS');
    res.set(
      'Access-Control-Allow-Headers',
      'Content-Type, Authorization, X-Supabase-Token, X-Runtime-Token'
    );
    res.set('Access-Control-Max-Age', '86400');
  }

  if (req.method === 'OPTIONS') {
    if (origin && !originAllowed(origin)) {
      return res.status(403).end();
    }
    return res.status(204).end();
  }

  next();
});

app.use(express.json({ limit: '128kb', strict: true }));

app.use((req, res, next) => {
  res.set('X-Content-Type-Options', 'nosniff');
  res.set('X-Frame-Options', 'DENY');
  res.set('Referrer-Policy', 'no-referrer');
  res.set('Cross-Origin-Opener-Policy', 'same-origin-allow-popups');
  res.set('Permissions-Policy', 'camera=(self), microphone=(), geolocation=(), payment=(), usb=()');
  res.set(
    'Content-Security-Policy',
    "default-src 'self'; " +
    "script-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net; " +
    "style-src 'self' 'unsafe-inline'; " +
    "img-src 'self' data: blob: https:; " +
    "font-src 'self' data:; " +
    "connect-src 'self' https://hwalhozxgkxydpddvfwa.supabase.co wss://hwalhozxgkxydpddvfwa.supabase.co; " +
    "object-src 'none'; base-uri 'self'; frame-ancestors 'none';"
  );

  if (String(req.headers['x-forwarded-proto'] || '').toLowerCase() === 'https') {
    res.set('Strict-Transport-Security', 'max-age=15552000; includeSubDomains');
  }

  next();
});

const httpServer = http.createServer(app);
const io = new Server(httpServer, {
  cors: {
    origin(origin, callback) {
      if (originAllowed(origin)) return callback(null, true);
      return callback(new Error('Origin não permitida pelo WildSnake.'));
    },
    methods: ['GET', 'POST'],
    credentials: false
  },
  transports: ['websocket', 'polling'],
  allowUpgrades: true,
  pingInterval: 10000,
  pingTimeout: 8000,
  connectTimeout: 12000,
  maxHttpBufferSize: 256 * 1024
});

/* =========================================================
   WILDSNAKE SERVER CONFIG
========================================================= */

const PORT = Number(process.env.PORT || 3000);
const GAME_VERSION = 'v13.33.0';
const BUILD = 'wildsnake-v13.33.0-low-latency-cache-broadphase';

const WORLD_RADIUS = 4200;
const SAFE_RADIUS = 3900;
const BASE_SPEED = 155;
const BOOST_MULT = 1.85;
const MIN_LENGTH = 16;
const SEGMENT_SPACING = 13;

// Física continua suave no servidor, rede mais leve.
const TICK_RATE = 30;
const WORLD_BROADCAST_RATE = 12;
const FOOD_BROADCAST_RATE = 2;

const FOOD_TARGET = 180;
const FOOD_HARD_LIMIT = 340;
const MAX_ROOM_PLAYERS = 35;
const PUBLIC_BOT_TARGET_TOTAL = 10;
const SOLO_NOTICE_DELAY_MS = 2200;
const HUMAN_INPUT_TIMEOUT_MS = 1500;

const HEAD_RADIUS = 16;
const BODY_RADIUS = 12;
const HEAD_HEAD_DISTANCE = HEAD_RADIUS * 2 - 1;
const HEAD_BODY_DISTANCE = HEAD_RADIUS + BODY_RADIUS + 2;

const players = new Map();
const privateRooms = new Map();
const publicRooms = new Map();


/* =========================================================
   V13.00.2 - PERSISTÊNCIA LEVE / CONTAS / LOJA LIMITADA
========================================================= */

/*
    IMPORTANTE:
    - Este armazenamento serve para desenvolvimento e testes locais.
    - Para produção real, troque por PostgreSQL/Supabase/etc.
    - Senhas locais são guardadas como hash scrypt, nunca em texto puro.
*/

const DATA_DIR =
  path.join(
    __dirname,
    'data'
  );

const STATE_FILE =
  path.join(
    DATA_DIR,
    'wildsnake_state.json'
  );

const BUG_REPORT_EMAIL =
  'pedrohenriquesousadeoliveiraph@gmail.com';

const SESSION_TTL_MS =
  1000 * 60 * 60 * 24 * 14;

const MAX_BUG_TEXT =
  4000;

const MAX_USERNAME_LENGTH =
  24;

const MIN_PASSWORD_LENGTH =
  10;

const sessions =
  new Map();

/*
   V13.15 - UMA CONTA = UM NAVEGADOR ATIVO
   ---------------------------------------------------------
   activeAccountSessions:
     accountId -> token + sockets atualmente vinculados.

   pendingSessionTransfers:
     pedido criado quando um segundo navegador tenta entrar.

   revokedSessionTokens:
     tokens invalidados durante troca de navegador/logout.
*/
const activeAccountSessions =
  new Map();

const pendingSessionTransfers =
  new Map();

const revokedSessionTokens =
  new Set();

const accountReleaseTimers =
  new Map();

const SESSION_TRANSFER_TTL_MS =
  2 * 60 * 1000;

const SESSION_DISCONNECT_GRACE_MS =
  12 * 1000;


function cleanupSessionTransfers(){
  const now = Date.now();

  for(const [requestId, request] of pendingSessionTransfers){
    if(!request || now > Number(request.expiresAt || 0)){
      pendingSessionTransfers.delete(requestId);
    }
  }
}


function getActiveAccountSession(accountId){
  const key = String(accountId || '');
  if(!key) return null;
  return activeAccountSessions.get(key) || null;
}


function activateAccountSession(accountId, token){
  const key = String(accountId || '');
  const value = String(token || '');

  if(!key || !value) return null;

  const previous = activeAccountSessions.get(key);

  if(previous && previous.token === value){
    previous.lastSeenAt = Date.now();
    return previous;
  }

  const record = {
    accountId:key,
    token:value,
    socketIds:new Set(),
    createdAt:Date.now(),
    lastSeenAt:Date.now()
  };

  activeAccountSessions.set(key, record);

  const timer = accountReleaseTimers.get(key);
  if(timer){
    clearTimeout(timer);
    accountReleaseTimers.delete(key);
  }

  return record;
}


function notifyActiveSessionTransfer(accountId, request){
  const active = getActiveAccountSession(accountId);
  if(!active) return;

  for(const socketId of active.socketIds){
    const target = io.sockets.sockets.get(socketId);

    if(target){
      target.emit('sessionTransferRequested', {
        requestId:request.requestId,
        createdAt:request.createdAt,
        expiresAt:request.expiresAt,
        message:'Outro navegador está tentando entrar nesta conta.',
        version:GAME_VERSION
      });
    }
  }
}


function createSessionTransferRequest(accountId){
  cleanupSessionTransfers();

  const key = String(accountId || '');

  for(const request of pendingSessionTransfers.values()){
    if(
      request.accountId === key
      &&
      request.status === 'pending'
      &&
      Date.now() <= request.expiresAt
    ){
      notifyActiveSessionTransfer(key, request);
      return request;
    }
  }

  const requestId = crypto.randomUUID();

  const request = {
    requestId,
    accountId:key,
    status:'pending',
    createdAt:Date.now(),
    expiresAt:Date.now() + SESSION_TRANSFER_TTL_MS,
    approvedAt:null,
    deniedAt:null
  };

  pendingSessionTransfers.set(requestId, request);
  notifyActiveSessionTransfer(key, request);

  return request;
}


function revokeAccountSession(accountId, reason='replaced'){
  const key = String(accountId || '');
  const active = activeAccountSessions.get(key);

  if(!active) return;

  revokedSessionTokens.add(active.token);
  sessions.delete(active.token);

  for(const socketId of [...active.socketIds]){
    const target = io.sockets.sockets.get(socketId);

    if(target){
      target.emit('sessionReplaced', {
        reason,
        message:
          reason === 'transfer'
            ? 'Sua conta foi transferida para outro navegador.'
            : 'Sua sessão foi encerrada.',
        version:GAME_VERSION
      });

      setTimeout(()=>{
        try{
          target.disconnect(true);
        }catch{}
      },250);
    }
  }

  activeAccountSessions.delete(key);

  const timer = accountReleaseTimers.get(key);
  if(timer){
    clearTimeout(timer);
    accountReleaseTimers.delete(key);
  }
}


function scheduleAccountSessionRelease(accountId, token){
  const key = String(accountId || '');
  if(!key) return;

  const oldTimer = accountReleaseTimers.get(key);
  if(oldTimer) clearTimeout(oldTimer);

  const timer = setTimeout(()=>{
    const active = activeAccountSessions.get(key);

    if(
      active
      &&
      active.token === token
      &&
      active.socketIds.size === 0
    ){
      activeAccountSessions.delete(key);
    }

    accountReleaseTimers.delete(key);
  },SESSION_DISCONNECT_GRACE_MS);

  accountReleaseTimers.set(key,timer);
}


const rateBuckets =
  new Map();


const LIMITED_SKIN_CATALOG = {

  celestialUnicorn:{
    id:'celestialUnicorn',
    name:'Unicórnio Celestial',
    currency:'gem',
    price:1250,
    stockMax:250
  },

  solarPhoenix:{
    id:'solarPhoenix',
    name:'Fênix Solar',
    currency:'gem',
    price:1450,
    stockMax:180
  },

  emperorLion:{
    id:'emperorLion',
    name:'Leão Imperador',
    currency:'gem',
    price:1650,
    stockMax:120
  },

  astralDragon:{
    id:'astralDragon',
    name:'Dragão Astral',
    currency:'gem',
    price:2200,
    stockMax:75
  }

};


function ensureDataDir(){

  try{

    fs.mkdirSync(
      DATA_DIR,
      {
        recursive:true
      }
    );

  }
  catch(
    error
  ){

    console.error(
      'Falha ao criar pasta data:',
      error.message
    );

  }

}


function defaultPersistentState(){

  const limitedInventory =
    {};

  for(
    const skin
    of
    Object.values(
      LIMITED_SKIN_CATALOG
    )
  ){

    limitedInventory[
      skin.id
    ] = {

      stock:
        skin.stockMax,

      owners:
        []

    };

  }

  return {

    schemaVersion:
      2,

    createdAt:
      new Date().toISOString(),

    accounts:
      {},

    limitedInventory,

    bugReports:
      []

  };

}


function normalizePersistentState(
  raw
){

  const state =
    raw
    &&
    typeof raw ===
    'object'
    ?
    raw
    :
    defaultPersistentState();

  state.schemaVersion =
    2;

  state.accounts =
    state.accounts
    &&
    typeof state.accounts ===
    'object'
    ?
    state.accounts
    :
    {};

  state.bugReports =
    Array.isArray(
      state.bugReports
    )
    ?
    state.bugReports
    :
    [];

  state.limitedInventory =
    state.limitedInventory
    &&
    typeof state.limitedInventory ===
    'object'
    ?
    state.limitedInventory
    :
    {};

  for(
    const skin
    of
    Object.values(
      LIMITED_SKIN_CATALOG
    )
  ){

    const current =
      state.limitedInventory[
        skin.id
      ];

    if(
      !current
      ||
      typeof current !==
      'object'
    ){

      state.limitedInventory[
        skin.id
      ] = {

        stock:
          skin.stockMax,

        owners:
          []

      };

      continue;

    }

    current.stock =
      clamp(
        Number(
          current.stock
        )
        ||
        0,
        0,
        skin.stockMax
      );

    current.owners =
      Array.isArray(
        current.owners
      )
      ?
      current.owners
      :
      [];

  }

  return state;

}


function loadPersistentState(){

  ensureDataDir();

  try{

    if(
      !fs.existsSync(
        STATE_FILE
      )
    ){

      const fresh =
        defaultPersistentState();

      fs.writeFileSync(
        STATE_FILE,
        JSON.stringify(
          fresh,
          null,
          2
        ),
        'utf8'
      );

      return fresh;

    }

    const parsed =
      JSON.parse(
        fs.readFileSync(
          STATE_FILE,
          'utf8'
        )
      );

    return normalizePersistentState(
      parsed
    );

  }
  catch(
    error
  ){

    console.error(
      'Falha ao carregar wildsnake_state.json:',
      error.message
    );

    return defaultPersistentState();

  }

}


let persistentState =
  loadPersistentState();


function savePersistentState(){

  ensureDataDir();

  const temp =
    STATE_FILE
    +
    '.tmp';

  try{

    fs.writeFileSync(
      temp,
      JSON.stringify(
        persistentState,
        null,
        2
      ),
      'utf8'
    );

    fs.renameSync(
      temp,
      STATE_FILE
    );

    return true;

  }
  catch(
    error
  ){

    console.error(
      'Falha ao salvar estado:',
      error.message
    );

    try{

      if(
        fs.existsSync(
          temp
        )
      ){

        fs.unlinkSync(
          temp
        );

      }

    }
    catch{}

    return false;

  }

}


function cleanUsername(
  value
){

  return String(
    value
    ??
    ''
  )
  .trim()
  .toLowerCase()
  .replace(
    /[^a-z0-9_.-]/g,
    ''
  )
  .slice(
    0,
    MAX_USERNAME_LENGTH
  );

}


function cleanDisplayName(
  value
){

  return String(
    value
    ??
    ''
  )
  .replace(
    /[<>]/g,
    ''
  )
  .trim()
  .slice(
    0,
    24
  );

}


function passwordLooksValid(
  password
){

  return (
    typeof password ===
    'string'
    &&
    password.length >=
    MIN_PASSWORD_LENGTH
    &&
    password.length <=
    128
  );

}


function scryptHash(
  password,
  salt
){

  return new Promise(
    (
      resolve,
      reject
    )=>{

      crypto.scrypt(
        password,
        salt,
        64,
        (
          error,
          derivedKey
        )=>{

          if(
            error
          ){

            reject(
              error
            );

            return;

          }

          resolve(
            derivedKey.toString(
              'hex'
            )
          );

        }
      );

    }
  );

}


function safeEqualHex(
  a,
  b
){

  try{

    const aa =
      Buffer.from(
        String(
          a
        ),
        'hex'
      );

    const bb =
      Buffer.from(
        String(
          b
        ),
        'hex'
      );

    if(
      aa.length !==
      bb.length
    ){

      return false;

    }

    return crypto.timingSafeEqual(
      aa,
      bb
    );

  }
  catch{

    return false;

  }

}


const FALLBACK_SESSION_SECRET =
  crypto.randomBytes(32).toString('hex');

function sessionSigningSecret(){
  return String(
    process.env.WILDSNAKE_SESSION_SECRET ||
    process.env.SUPABASE_SECRET_KEY ||
    process.env.SUPABASE_SERVICE_ROLE_KEY ||
    process.env.SUPABASE_ADMIN_KEY ||
    process.env.WILDSNAKE_SUPABASE_SECRET_KEY ||
    FALLBACK_SESSION_SECRET
  );
}

function sessionSignature(payloadPart){
  return crypto
    .createHmac('sha256',sessionSigningSecret())
    .update(payloadPart)
    .digest('base64url');
}

function createSession(
  accountId,
  role='player'
){

  const now=Date.now();

  const payload={
    a:String(accountId),
    r:String(role||'player'),
    i:now,
    e:now+SESSION_TTL_MS
  };

  const payloadPart=
    Buffer.from(
      JSON.stringify(payload),
      'utf8'
    ).toString('base64url');

  const token=
    `ws1.${payloadPart}.${sessionSignature(payloadPart)}`;

  const session={
    token,
    accountId:payload.a,
    role:payload.r,
    createdAt:payload.i,
    expiresAt:payload.e
  };

  /*
     Mantém cache em memória para velocidade, mas o token é assinado.
     Se o Render reiniciar, a sessão continua válida porque pode ser
     verificada novamente usando a mesma Secret Key.
  */
  sessions.set(token,session);

  return token;
}


function parseSignedSessionToken(token){
  const value=String(token||'').trim();

  if(!value.startsWith('ws1.')){
    return null;
  }

  const parts=value.split('.');

  if(parts.length!==3){
    return null;
  }

  const payloadPart=parts[1];
  const signature=parts[2];
  const expected=sessionSignature(payloadPart);

  try{
    const a=Buffer.from(signature);
    const b=Buffer.from(expected);

    if(a.length!==b.length || !crypto.timingSafeEqual(a,b)){
      return null;
    }
  }catch{
    return null;
  }

  try{
    const payload=JSON.parse(
      Buffer.from(payloadPart,'base64url').toString('utf8')
    );

    if(
      !payload?.a ||
      !Number.isFinite(Number(payload?.e)) ||
      Date.now()>Number(payload.e)
    ){
      return null;
    }

    return{
      token:value,
      accountId:String(payload.a),
      role:String(payload.r||'player'),
      createdAt:Number(payload.i||Date.now()),
      expiresAt:Number(payload.e)
    };
  }catch{
    return null;
  }
}


function readBearerToken(
  req
){

  const header =
    String(
      req.headers.authorization
      ||
      ''
    );

  if(
    !header.toLowerCase().startsWith(
      'bearer '
    )
  ){

    return null;

  }

  return header.slice(
    7
  )
  .trim()
  ||
  null;

}


function sessionFromRequest(
  req
){

  return sessionFromToken(
    readBearerToken(req)
  );

}


function publicAccountView(
  account
){

  if(
    !account
  ){

    return null;

  }

  return {

    id:
      account.id,

    username:
      account.username,

    displayName:
      account.displayName,

    createdAt:
      account.createdAt,

    role:
      account.role
      ||
      'player',

    provider:
      account.provider
      ||
      'local'

  };

}


function createLocalAccountRecord(
  username,
  displayName,
  salt,
  passwordHash
){

  const id =
    uid(
      'ACC'
    );

  return {

    id,

    username,

    displayName:
      displayName
      ||
      username,

    salt,

    passwordHash,

    createdAt:
      new Date().toISOString(),

    role:
      'player',

    provider:
      'local',

    lastLoginAt:
      null

  };

}


async function registerLocalAccount({
  username,
  password,
  displayName
}){

  const normalized =
    cleanUsername(
      username
    );

  if(
    normalized.length <
    3
  ){

    return {
      ok:false,
      error:'O usuário precisa ter pelo menos 3 caracteres.'
    };

  }

  if(
    !passwordLooksValid(
      password
    )
  ){

    return {
      ok:false,
      error:`A senha precisa ter pelo menos ${MIN_PASSWORD_LENGTH} caracteres.`
    };

  }

  if(
    Object.values(
      persistentState.accounts
    )
    .some(
      account =>
        account.username ===
        normalized
    )
  ){

    return {
      ok:false,
      error:'Este nome de usuário já existe.'
    };

  }

  const salt =
    crypto.randomBytes(
      16
    )
    .toString(
      'hex'
    );

  const passwordHash =
    await scryptHash(
      password,
      salt
    );

  const account =
    createLocalAccountRecord(

      normalized,

      cleanDisplayName(
        displayName
      )
      ||
      normalized,

      salt,

      passwordHash

    );

  persistentState.accounts[
    account.id
  ] =
    account;

  savePersistentState();

  const token =
    createSession(
      account.id,
      account.role
    );

  return {

    ok:true,

    token,

    account:
      publicAccountView(
        account
      )

  };

}


async function loginLocalAccount({
  username,
  password
}){

  const normalized =
    cleanUsername(
      username
    );

  const account =
    Object.values(
      persistentState.accounts
    )
    .find(
      item =>
        item.username ===
        normalized
    );

  if(
    !account
  ){

    return {
      ok:false,
      error:'Usuário ou senha inválidos.'
    };

  }

  const candidate =
    await scryptHash(
      String(
        password
        ??
        ''
      ),
      account.salt
    );

  if(
    !safeEqualHex(
      candidate,
      account.passwordHash
    )
  ){

    return {
      ok:false,
      error:'Usuário ou senha inválidos.'
    };

  }

  account.lastLoginAt =
    new Date().toISOString();

  savePersistentState();

  const token =
    createSession(
      account.id,
      account.role
      ||
      'player'
    );

  return {

    ok:true,

    token,

    account:
      publicAccountView(
        account
      )

  };

}


function rateLimit(
  key,
  {
    windowMs,
    max
  }
){

  const now =
    Date.now();

  const current =
    rateBuckets.get(
      key
    );

  if(
    !current
    ||
    now -
    current.startedAt
    >
    windowMs
  ){

    rateBuckets.set(
      key,
      {
        startedAt:
          now,

        count:
          1
      }
    );

    return true;

  }

  if(
    current.count >=
    max
  ){

    return false;

  }

  current.count++;

  return true;

}


function limitedCatalogView(){

  return Object.values(
    LIMITED_SKIN_CATALOG
  )
  .map(
    skin => {

      const inventory =
        persistentState.limitedInventory[
          skin.id
        ]
        ||
        {
          stock:0,
          owners:[]
        };

      return {

        id:
          skin.id,

        name:
          skin.name,

        currency:
          skin.currency,

        price:
          skin.price,

        stock:
          inventory.stock,

        stockMax:
          skin.stockMax

      };

    }
  );

}


function buyLimitedSkinForProfile(
  skinId,
  profileId
){

  const skin =
    LIMITED_SKIN_CATALOG[
      skinId
    ];

  if(
    !skin
  ){

    return {
      ok:false,
      error:'Skin limitada inválida.'
    };

  }

  const inventory =
    persistentState.limitedInventory[
      skinId
    ];

  const buyer =
    String(
      profileId
      ||
      ''
    )
    .trim()
    .slice(
      0,
      100
    );

  if(
    !buyer
  ){

    return {
      ok:false,
      error:'Perfil de compra inválido.'
    };

  }

  if(
    inventory.owners.includes(
      buyer
    )
  ){

    return {
      ok:false,
      error:'Este perfil já possui esta skin limitada.'
    };

  }

  if(
    inventory.stock <=
    0
  ){

    return {
      ok:false,
      error:'ESGOTADA'
    };

  }

  inventory.stock--;

  inventory.owners.push(
    buyer
  );

  savePersistentState();

  return {

    ok:true,

    skinId,

    remaining:
      inventory.stock,

    stockMax:
      skin.stockMax

  };

}


/* =========================================================
   V13.10 - SUPABASE SEGURO / CONTA / ECONOMIA / TUTORIAL
========================================================= */

const SUPABASE_URL = String(
  process.env.SUPABASE_URL ||
  'https://hwalhozxgkxydpddvfwa.supabase.co'
).replace(/\/+$/, '');

const SUPABASE_PUBLISHABLE_KEY = String(
  process.env.SUPABASE_PUBLISHABLE_KEY ||
  process.env.SUPABASE_ANON_KEY ||
  process.env.WILDSNAKE_SUPABASE_PUBLISHABLE_KEY ||
  ''
).trim();

const SUPABASE_ADMIN_KEY = String(
  process.env.SUPABASE_SECRET_KEY ||
  process.env.SUPABASE_SERVICE_ROLE_KEY ||
  process.env.SUPABASE_ADMIN_KEY ||
  process.env.WILDSNAKE_SUPABASE_SECRET_KEY ||
  ''
).trim();

const RUNTIME_DEBUG_TOKEN = String(
  process.env.RUNTIME_DEBUG_TOKEN || ''
).trim();

const SECURE_DB_TABLES = Object.freeze({
  accounts: 'game_accounts',
  wallets: 'game_wallets',
  skins: 'game_skins',
  catalog: 'game_skin_catalog',
  ledger: 'game_economy_ledger'
});

const TUTORIAL_SKIN_ODDS = Object.freeze([
  { rarity: 'limited', label: 'LIMITADA', weight: 5 },
  { rarity: 'mythic', label: 'MÍTICA', weight: 8 },
  { rarity: 'legendary', label: 'LENDÁRIA', weight: 17 },
  { rarity: 'epic', label: 'ÉPICA', weight: 30 },
  { rarity: 'rare', label: 'RARA', weight: 40 }
]);


/* =========================================================
   V13.17 - ECONOMIA / COMBOS / CAMINHO DE RECOMPENSAS
   Regra central: 1 WildGem = 100 WildCoins.
   O navegador apenas anima; compra, roleta e resgate são
   validados e gravados pelo servidor/Supabase.
========================================================= */

const WILD_GEM_COIN_VALUE = 100;

const SHOP_COMBOS = Object.freeze({
  wildAnimalCombo:Object.freeze({
    id:'wildAnimalCombo',
    name:'Combo Animais Selvagens',
    subtitle:'COMBO ORIGINAL',
    badge:'EXCLUSIVO',
    accent:'#55d98b',
    coinPrice:50_000,
    gemPrice:500,
    skins:Object.freeze([
      'crocodile',
      'bat',
      'scorpion',
      'cow',
      'cockatielLutino',
      'cockatielPearl'
    ])
  }),

  lunarEventCombo:Object.freeze({
    id:'lunarEventCombo',
    name:'Combo Evento Lunar',
    subtitle:'EVENTO LUNAR',
    badge:'PROMOÇÃO',
    accent:'#ff384d',
    coinPrice:75_000,
    gemPrice:750,
    skins:Object.freeze([
      'lunarDragon',
      'lunarJadeRabbit',
      'lunarTiger'
    ])
  })
});

const WILD_ANIMAL_COMBO = SHOP_COMBOS.wildAnimalCombo;

const COMBO_ONLY_SKIN_IDS = new Set(
  Object.values(SHOP_COMBOS).flatMap(combo => combo.skins)
);

/*
   Catálogo autoritativo das skins AVULSAS não limitadas.
   Regra de preço V13.17:
   - Comum / Rara / Épica: WildCoins.
   - Lendária / Mítica: WildGems.
   - 1 WildGem = 100 WildCoins.
   O preço é definido pelo valor visual real, não apenas pelo nome da raridade.
*/
const SHOP_SKIN_CATALOG = Object.freeze({
  fish:{ id:'fish', name:'Peixe Tropical', currency:'coin', price:7000, rarity:'rare', active:true },
  shark:{ id:'shark', name:'Tubarão Azul', currency:'coin', price:15000, rarity:'epic', active:true },
  venom:{ id:'venom', name:'Cobra Venenosa', currency:'coin', price:16000, rarity:'epic', active:true },
  dragon:{ id:'dragon', name:'Dragão Verde', currency:'coin', price:18000, rarity:'epic', active:true },
  lion:{ id:'lion', name:'Rei Leão', currency:'coin', price:16000, rarity:'epic', active:true },
  robot:{ id:'robot', name:'Cyber Snake', currency:'gem', price:300, rarity:'legendary', active:true },
  robotPink:{ id:'robotPink', name:'Cyber Pink', currency:'gem', price:300, rarity:'legendary', active:true },
  retro:{ id:'retro', name:'Retro Wave', currency:'coin', price:8000, rarity:'rare', active:true },
  rainbow:{ id:'rainbow', name:'Rainbow 90s', currency:'coin', price:10000, rarity:'rare', active:true },
  arcade:{ id:'arcade', name:'Arcade Neon', currency:'coin', price:15000, rarity:'epic', active:true },
  disco:{ id:'disco', name:'Disco Snake', currency:'coin', price:18000, rarity:'epic', active:true },
  tiger:{ id:'tiger', name:'Tigre Imperial', currency:'coin', price:15000, rarity:'epic', active:true },
  wolf:{ id:'wolf', name:'Lobo Lunar', currency:'coin', price:18000, rarity:'epic', active:true },
  panda:{ id:'panda', name:'Panda Real', currency:'coin', price:8000, rarity:'rare', active:true },
  axolotl:{ id:'axolotl', name:'Axolote Rosa', currency:'coin', price:15000, rarity:'epic', active:true },
  peacock:{ id:'peacock', name:'Pavão Esmeralda', currency:'gem', price:330, rarity:'legendary', active:true },
  unicorn:{ id:'unicorn', name:'Unicórnio Aurora', currency:'gem', price:650, rarity:'mythic', active:true },
  iceDragon:{ id:'iceDragon', name:'Dragão de Gelo', currency:'gem', price:300, rarity:'legendary', active:true },
  horse:{ id:'horse', name:'Cavalo Selvagem', currency:'coin', price:14000, rarity:'epic', active:true },
  pig:{ id:'pig', name:'Porquinho Rosa', currency:'coin', price:7000, rarity:'rare', active:true },
  crow:{ id:'crow', name:'Corvo Sombrio', currency:'coin', price:18000, rarity:'epic', active:true },
  capybara:{ id:'capybara', name:'Capivara do Pantanal', currency:'coin', price:8500, rarity:'rare', active:true },
  alien:{ id:'alien', name:'Alien Nebuloso', currency:'gem', price:320, rarity:'legendary', active:true },
  octopus:{ id:'octopus', name:'Polvo Abissal', currency:'coin', price:18000, rarity:'epic', active:true },
  crab:{ id:'crab', name:'Caranguejo Rubi', currency:'coin', price:15000, rarity:'epic', active:true },
  lizard:{ id:'lizard', name:'Lagarto Esmeralda', currency:'coin', price:16000, rarity:'epic', active:true },
  fireDragon:{ id:'fireDragon', name:'Dragão de Fogo', currency:'gem', price:600, rarity:'mythic', active:true },

  crocodile:{ id:'crocodile', name:'Crocodilo', currency:'combo', price:0, rarity:'epic', active:true },
  bat:{ id:'bat', name:'Morcego', currency:'combo', price:0, rarity:'epic', active:true },
  scorpion:{ id:'scorpion', name:'Escorpião', currency:'combo', price:0, rarity:'legendary', active:true },
  cow:{ id:'cow', name:'Vaquinha', currency:'combo', price:0, rarity:'rare', active:true },
  cockatielLutino:{ id:'cockatielLutino', name:'Calopsita Lutina', currency:'combo', price:0, rarity:'legendary', active:true },
  cockatielPearl:{ id:'cockatielPearl', name:'Calopsita Pérola', currency:'combo', price:0, rarity:'legendary', active:true },

  lunarDragon:{ id:'lunarDragon', name:'Dragão Lunar', currency:'combo', price:0, rarity:'mythic', active:true },
  lunarJadeRabbit:{ id:'lunarJadeRabbit', name:'Coelho de Jade', currency:'combo', price:0, rarity:'mythic', active:true },
  lunarTiger:{ id:'lunarTiger', name:'Tigre Lunar Imperial', currency:'combo', price:0, rarity:'mythic', active:true }
});


const SHOP_MONEY_PACKS = Object.freeze([
  { id:'coins15000', kind:'currency', type:'coin', title:'Coins Inicial', amount:15_000, bonus:0, cash:3.90, badge:'', featured:false },
  { id:'coins50000', kind:'currency', type:'coin', title:'Coins Popular', amount:50_000, bonus:10_000, cash:7.90, badge:'MAIS VENDIDO', featured:true },
  { id:'coins100000', kind:'currency', type:'coin', title:'Coins Turbo', amount:100_000, bonus:25_000, cash:12.90, badge:'+25.000 BÔNUS', featured:false },
  { id:'coins250000', kind:'currency', type:'coin', title:'Coins Mega', amount:250_000, bonus:75_000, cash:19.90, badge:'MELHOR VALOR', featured:true },

  { id:'gems300', kind:'currency', type:'gem', title:'Gems Mini', amount:300, bonus:0, cash:5.90, badge:'', featured:false },
  { id:'gems600', kind:'currency', type:'gem', title:'Gems Starter', amount:600, bonus:0, cash:9.90, badge:'', featured:false },
  { id:'gems1200', kind:'currency', type:'gem', title:'Gems Popular', amount:1_200, bonus:0, cash:15.50, badge:'MAIS VENDIDO', featured:true },
  { id:'gems2000', kind:'currency', type:'gem', title:'Gems Turbo', amount:2_000, bonus:200, cash:19.90, badge:'+200 BÔNUS', featured:false },
  { id:'gems3000', kind:'currency', type:'gem', title:'Gems Premium', amount:3_000, bonus:400, cash:24.90, badge:'+400 BÔNUS', featured:false },
  { id:'gems5000', kind:'currency', type:'gem', title:'Gems Mega', amount:5_000, bonus:800, cash:29.90, badge:'MELHOR VALOR', featured:true },

  { id:'rouletteStarter', kind:'roulette', type:'mixed', title:'Roleta Starter', cash:6.90, badge:'1 SKIN + BÔNUS', featured:false, coinBonus:10_000, gemBonus:0, rarityFloor:'rare' },
  { id:'rouletteTurbo', kind:'roulette', type:'mixed', title:'Roleta Turbo', cash:14.90, badge:'RECOMENDADO', featured:true, coinBonus:35_000, gemBonus:300, rarityFloor:'rare' },
  { id:'rouletteElite', kind:'roulette', type:'mixed', title:'Roleta Elite', cash:24.90, badge:'CHANCE PREMIUM', featured:false, coinBonus:75_000, gemBonus:800, rarityFloor:'epic' }
]);

let shopCatalogSyncPromise = null;

async function ensureAuthoritativeShopCatalog() {
  if (!secureDbReady()) return false;
  if (shopCatalogSyncPromise) return shopCatalogSyncPromise;

  shopCatalogSyncPromise = Promise.all(
    Object.values(SHOP_SKIN_CATALOG).map(skin =>
      dbInsert(
        SECURE_DB_TABLES.catalog,
        {
          skin_id:skin.id,
          name:skin.name,
          currency:skin.currency,
          price:skin.price,
          rarity:skin.rarity,
          limited:false,
          active:skin.active !== false
        },
        { upsert:true, onConflict:'skin_id' }
      )
    )
  )
    .then(() => true)
    .catch(error => {
      shopCatalogSyncPromise = null;
      console.error('shop catalog sync:', error?.message || error);
      throw error;
    });

  return shopCatalogSyncPromise;
}

const PROGRESSION_SKIN_ODDS = Object.freeze([
  { rarity:'common', label:'COMUM', weight:45 },
  { rarity:'rare', label:'RARA', weight:30 },
  { rarity:'epic', label:'ÉPICA', weight:17 },
  { rarity:'legendary', label:'LENDÁRIA', weight:6 },
  { rarity:'mythic', label:'MÍTICA', weight:2 }
]);

const PROGRESSION_WORLDS = Object.freeze([
  {
    id:'world1',
    index:1,
    name:'Selva do Despertar',
    subtitle:'Recompensas rápidas para começar forte.',
    theme:'jungle',
    icon:'🌿',
    unlockXp:0,
    endXp:20_000
  },
  {
    id:'world2',
    index:2,
    name:'Órbita Neon',
    subtitle:'O ritmo desacelera e as conquistas ficam mais valiosas.',
    theme:'cosmic',
    icon:'🌌',
    unlockXp:20_000,
    endXp:65_000
  },
  {
    id:'world3',
    index:3,
    name:'Fenda Vulcânica',
    subtitle:'Mais XP por etapa e recompensas especiais mais espaçadas.',
    theme:'magma',
    icon:'🌋',
    unlockXp:65_000,
    endXp:150_000
  },
  {
    id:'world4',
    index:4,
    name:'Reino Congelado',
    subtitle:'Uma trilha longa para jogadores persistentes.',
    theme:'frost',
    icon:'❄️',
    unlockXp:150_000,
    endXp:300_000
  },
  {
    id:'world5',
    index:5,
    name:'Vazio Astral',
    subtitle:'O mundo mais difícil da primeira temporada.',
    theme:'void',
    icon:'🕳️',
    unlockXp:300_000,
    endXp:600_000
  }
]);

function totalXpRequiredForLevel(level) {
  const safeLevel = Math.max(1, Math.floor(Number(level) || 1));
  const completedLevels = safeLevel - 1;

  // Soma: 500 + 750 + 1000 + ... até o nível anterior.
  return (
    500 * completedLevels
    +
    125 * completedLevels * Math.max(0, completedLevels - 1)
  );
}

function totalXpForWallet(wallet) {
  const level = Math.max(1, Math.floor(Number(wallet?.level) || 1));
  const currentXp = Math.max(0, Math.floor(Number(wallet?.xp) || 0));
  return totalXpRequiredForLevel(level) + currentXp;
}

function progressionRewardForLevel(level, worldIndex, ordinal) {
  const safeWorld = Math.max(1, Number(worldIndex) || 1);
  const safeOrdinal = Math.max(1, Number(ordinal) || 1);

  if (safeWorld === 1 && safeOrdinal === 1) {
    return {
      kind:'coins',
      icon:'🪙',
      coins:150,
      gems:0,
      label:'150 WildCoins'
    };
  }

  if (safeOrdinal % 9 === 0) {
    return {
      kind:'gift',
      icon:'🎁',
      coins:600 + safeWorld * 350,
      gems:3 + safeWorld * 2,
      skinChoice:['rare','epic'],
      label:'Presente Especial'
    };
  }

  if (safeOrdinal % 5 === 0) {
    return {
      kind:'skin_roll',
      icon:'🎰',
      coins:0,
      gems:0,
      label:'Roleta de Skin'
    };
  }

  if (safeOrdinal % 3 === 0) {
    const gems = 2 + safeWorld * 2;
    return {
      kind:'gems',
      icon:'💎',
      coins:0,
      gems,
      label:`${gems} WildGems`
    };
  }

  const coins = Math.round(
    150
    + safeWorld * 120
    + Math.min(1_700, safeOrdinal * (55 + safeWorld * 8))
  );

  return {
    kind:'coins',
    icon:'🪙',
    coins,
    gems:0,
    label:`${coins.toLocaleString('pt-BR')} WildCoins`
  };
}

function progressionWorldFinalReward(world) {
  const idx = Math.max(1, Number(world?.index) || 1);
  const table = {
    1:{ coins:1_500, gems:10 },
    2:{ coins:2_500, gems:15 },
    3:{ coins:3_500, gems:20 },
    4:{ coins:5_000, gems:30 },
    5:{ coins:8_000, gems:50 }
  };
  const reward = table[idx] || table[5];

  return {
    kind:'gift',
    icon:'👑',
    coins:reward.coins,
    gems:reward.gems,
    skinChoice:['rare','epic'],
    label:'Baú do Mundo'
  };
}

function buildProgressionWorldDefinitions() {
  return PROGRESSION_WORLDS.map(world => {
    const nodes = [];
    let ordinal = 0;

    for (let level = 1; level <= 250; level++) {
      const xpRequired = totalXpRequiredForLevel(level);

      if (xpRequired < world.unlockXp) continue;
      if (xpRequired >= world.endXp) break;

      ordinal += 1;
      nodes.push({
        id:`${world.id}-level-${level}`,
        worldId:world.id,
        worldIndex:world.index,
        level,
        ordinal,
        xpRequired,
        final:false,
        reward:progressionRewardForLevel(level, world.index, ordinal)
      });
    }

    nodes.push({
      id:`${world.id}-final`,
      worldId:world.id,
      worldIndex:world.index,
      level:null,
      ordinal:ordinal + 1,
      xpRequired:world.endXp,
      final:true,
      reward:progressionWorldFinalReward(world)
    });

    return {
      ...world,
      nodes
    };
  });
}

const PROGRESSION_WORLD_DEFINITIONS = buildProgressionWorldDefinitions();
const PROGRESSION_NODE_MAP = new Map(
  PROGRESSION_WORLD_DEFINITIONS
    .flatMap(world => world.nodes)
    .map(node => [node.id,node])
);

function progressionNodeById(nodeId) {
  return PROGRESSION_NODE_MAP.get(String(nodeId || '')) || null;
}

function progressionOddsPublicView() {
  return PROGRESSION_SKIN_ODDS.map(item => ({
    rarity:item.rarity,
    label:item.label,
    percent:item.weight
  }));
}

async function progressionLedgerRows(accountId) {
  if (!accountId || !secureDbReady()) return [];

  return dbSelect(SECURE_DB_TABLES.ledger, {
    select:'event_type,idempotency_key,skin_id,metadata,created_at',
    account_id:`eq.${accountId}`,
    event_type:'in.(progression_reward,progression_skin_roll,progression_gift_skin)',
    order:'created_at.asc'
  });
}

function rewardRpcUnavailable(error) {
  const raw = String(error?.message || error || '').toLowerCase();
  return error?.status === 404
    || String(error?.code || '').toUpperCase() === 'PGRST202'
    || raw.includes('could not find the function')
    || raw.includes('function public.ws_claim_progression')
    || raw.includes('schema cache');
}

async function secureClaimProgressionCurrency(accountId, node) {
  if (!accountId) throw new Error('ACCOUNT_REQUIRED');
  if (!node?.id) throw new Error('RECOMPENSA_INVALIDA');
  if (!secureDbReady()) throw new Error('SUPABASE_SERVER_NOT_CONFIGURED');

  const reward = node.reward || {};

  try {
    const claim = await dbRpc('ws_claim_progression_currency', {
      p_account_id:accountId,
      p_node_id:node.id,
      p_coins:Math.max(0,Math.floor(Number(reward.coins) || 0)),
      p_gems:Math.max(0,Math.floor(Number(reward.gems) || 0)),
      p_metadata:{
        nodeId:node.id,
        worldId:node.worldId,
        worldIndex:node.worldIndex,
        level:node.level,
        xpRequired:node.xpRequired,
        final:!!node.final,
        kind:reward.kind,
        label:reward.label,
        skinChoice:Array.isArray(reward.skinChoice) ? reward.skinChoice : null
      }
    });
    return { reused:!!claim?.alreadyClaimed, reward, claim };
  } catch (error) {
    if (!rewardRpcUnavailable(error)) throw error;
    console.warn('reward claim RPC indisponível; usando fallback REST seguro:', error?.message || error);
  }

  return withMatchRewardLock(accountId, async () => {
    const idempotencyKey = `progression:${accountId}:${node.id}`;

    const previous = await dbSelect(SECURE_DB_TABLES.ledger, {
      select:'id,metadata,amount,currency,created_at',
      idempotency_key:`eq.${idempotencyKey}`,
      limit:1
    });

    if (previous.length) {
      return { reused:true, reward, claim:previous[0] };
    }

    const stateBefore = await loadSecureGameState(accountId);
    if (!stateBefore?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const wallet = stateBefore.wallet;
    const oldCoins = Math.max(0, Number(wallet.coins || 0));
    const oldGems = Math.max(0, Number(wallet.wildgems || 0));
    const coinsToAdd = Math.max(0, Math.floor(Number(reward.coins) || 0));
    const gemsToAdd = Math.max(0, Math.floor(Number(reward.gems) || 0));

    await dbUpdate(
      SECURE_DB_TABLES.wallets,
      { account_id:`eq.${accountId}` },
      {
        coins:oldCoins + coinsToAdd,
        wildgems:oldGems + gemsToAdd,
        updated_at:new Date().toISOString()
      }
    );

    let claim = null;
    try {
      const inserted = await dbInsert(SECURE_DB_TABLES.ledger, {
        account_id:accountId,
        event_type:'progression_reward',
        currency:'mixed',
        amount:coinsToAdd,
        idempotency_key:idempotencyKey,
        metadata:{
          nodeId:node.id,
          worldId:node.worldId,
          worldIndex:node.worldIndex,
          level:node.level,
          xpRequired:node.xpRequired,
          final:!!node.final,
          kind:reward.kind,
          label:reward.label,
          coins:coinsToAdd,
          gems:gemsToAdd,
          skinChoice:Array.isArray(reward.skinChoice) ? reward.skinChoice : null,
          creditedAt:new Date().toISOString()
        }
      });
      claim = inserted?.[0] || inserted || null;
    } catch (error) {
      if (error?.status === 409) {
        claim = (await dbSelect(SECURE_DB_TABLES.ledger, {
          select:'id,metadata,amount,currency,created_at',
          idempotency_key:`eq.${idempotencyKey}`,
          limit:1
        }))[0] || null;
      } else {
        await dbUpdate(
          SECURE_DB_TABLES.wallets,
          { account_id:`eq.${accountId}` },
          { coins:oldCoins, wildgems:oldGems, updated_at:new Date().toISOString() }
        ).catch(() => {});
        throw error;
      }
    }

    return { reused:false, reward, claim };
  });
}

async function secureClaimProgressionSkin(accountId, node, chosen) {
  if (!accountId) throw new Error('ACCOUNT_REQUIRED');
  if (!node?.id || !chosen?.skin_id) throw new Error('SKIN_INVALIDA');
  if (!secureDbReady()) throw new Error('SUPABASE_SERVER_NOT_CONFIGURED');

  try {
    const claim = await dbRpc('ws_claim_progression_skin', {
      p_account_id:accountId,
      p_node_id:node.id,
      p_skin_id:chosen.skin_id,
      p_metadata:{
        nodeId:node.id,
        worldId:node.worldId,
        worldIndex:node.worldIndex,
        level:node.level,
        xpRequired:node.xpRequired,
        kind:'skin_roll',
        skinId:chosen.skin_id,
        skinName:chosen.name,
        rarity:chosen.rarity
      }
    });
    return { reused:!!claim?.alreadyClaimed, claim, result:chosen };
  } catch (error) {
    if (!rewardRpcUnavailable(error)) throw error;
    console.warn('reward skin RPC indisponível; usando fallback REST:', error?.message || error);
  }

  return withMatchRewardLock(accountId, async () => {
    const idempotencyKey = `progression:${accountId}:${node.id}`;

    const previous = await dbSelect(SECURE_DB_TABLES.ledger, {
      select:'id,skin_id,metadata,created_at',
      idempotency_key:`eq.${idempotencyKey}`,
      limit:1
    });

    if (previous.length) {
      return {
        reused:true,
        claim:previous[0],
        result:{
          skin_id:String(previous[0]?.skin_id || previous[0]?.metadata?.skinId || chosen.skin_id),
          name:previous[0]?.metadata?.skinName || chosen.name,
          rarity:previous[0]?.metadata?.rarity || chosen.rarity
        }
      };
    }

    const stateBefore = await loadSecureGameState(accountId);
    if (!stateBefore?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const owned = new Set(Array.isArray(stateBefore.ownedSkins) ? stateBefore.ownedSkins : []);
    if (owned.has(String(chosen.skin_id || ''))) throw new Error('SKIN_JA_POSSUI');

    await dbInsert(SECURE_DB_TABLES.skins, {
      account_id:accountId,
      skin_id:chosen.skin_id,
      source:'progression_roll'
    });

    let claim = null;
    try {
      const inserted = await dbInsert(SECURE_DB_TABLES.ledger, {
        account_id:accountId,
        event_type:'progression_skin_roll',
        currency:null,
        amount:0,
        skin_id:chosen.skin_id,
        idempotency_key:idempotencyKey,
        metadata:{
          nodeId:node.id,
          worldId:node.worldId,
          worldIndex:node.worldIndex,
          level:node.level,
          xpRequired:node.xpRequired,
          kind:'skin_roll',
          skinId:chosen.skin_id,
          skinName:chosen.name,
          rarity:chosen.rarity,
          grantedAt:new Date().toISOString()
        }
      });
      claim = inserted?.[0] || inserted || null;
    } catch (error) {
      if (error?.status === 409) {
        claim = (await dbSelect(SECURE_DB_TABLES.ledger, {
          select:'id,skin_id,metadata,created_at',
          idempotency_key:`eq.${idempotencyKey}`,
          limit:1
        }))[0] || null;
      } else {
        await supabaseAdminRequest(
          `/rest/v1/${encodeURIComponent(SECURE_DB_TABLES.skins)}?account_id=eq.${encodeURIComponent(accountId)}&skin_id=eq.${encodeURIComponent(chosen.skin_id)}`,
          { method:'DELETE', headers:{ Prefer:'return=minimal' } }
        ).catch(() => {});
        throw error;
      }
    }

    return { reused:false, claim, result:chosen };
  });
}

async function secureClaimProgressionGiftSkin(accountId, node, skin) {
  if (!accountId) throw new Error('ACCOUNT_REQUIRED');
  if (!node?.id || !skin?.skin_id) throw new Error('SKIN_INVALIDA');
  if (!secureDbReady()) throw new Error('SUPABASE_SERVER_NOT_CONFIGURED');

  try {
    const claim = await dbRpc('ws_claim_progression_gift_skin', {
      p_account_id:accountId,
      p_node_id:node.id,
      p_skin_id:skin.skin_id,
      p_metadata:{
        nodeId:node.id,
        worldId:node.worldId,
        worldIndex:node.worldIndex,
        kind:'gift_skin_choice',
        skinId:skin.skin_id,
        skinName:skin.name,
        rarity:skin.rarity
      }
    });
    return { reused:!!claim?.alreadyClaimed, claim, result:skin };
  } catch (error) {
    if (!rewardRpcUnavailable(error)) throw error;
    console.warn('reward gift skin RPC indisponível; usando fallback REST:', error?.message || error);
  }

  return withMatchRewardLock(accountId, async () => {
    const rewardKey = `progression:${accountId}:${node.id}`;
    const giftKey = `gift-skin:${accountId}:${node.id}`;

    const rewardClaim = await dbSelect(SECURE_DB_TABLES.ledger, {
      select:'id,metadata',
      idempotency_key:`eq.${rewardKey}`,
      limit:1
    });
    if (!rewardClaim.length) throw new Error('PRESENTE_NAO_RESGATADO');

    const previous = await dbSelect(SECURE_DB_TABLES.ledger, {
      select:'id,skin_id,metadata,created_at',
      idempotency_key:`eq.${giftKey}`,
      limit:1
    });
    if (previous.length) {
      return { reused:true, claim:previous[0], result:skin };
    }

    const stateBefore = await loadSecureGameState(accountId);
    if (!stateBefore?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const owned = new Set(Array.isArray(stateBefore.ownedSkins) ? stateBefore.ownedSkins : []);
    if (owned.has(String(skin.skin_id || ''))) throw new Error('SKIN_JA_POSSUI');

    await dbInsert(SECURE_DB_TABLES.skins, {
      account_id:accountId,
      skin_id:skin.skin_id,
      source:'progression_gift'
    });

    let claim = null;
    try {
      const inserted = await dbInsert(SECURE_DB_TABLES.ledger, {
        account_id:accountId,
        event_type:'progression_gift_skin',
        currency:null,
        amount:0,
        skin_id:skin.skin_id,
        idempotency_key:giftKey,
        metadata:{
          nodeId:node.id,
          worldId:node.worldId,
          worldIndex:node.worldIndex,
          kind:'gift_skin_choice',
          skinId:skin.skin_id,
          skinName:skin.name,
          rarity:skin.rarity,
          grantedAt:new Date().toISOString()
        }
      });
      claim = inserted?.[0] || inserted || null;
    } catch (error) {
      if (error?.status === 409) {
        claim = (await dbSelect(SECURE_DB_TABLES.ledger, {
          select:'id,skin_id,metadata,created_at',
          idempotency_key:`eq.${giftKey}`,
          limit:1
        }))[0] || null;
      } else {
        await supabaseAdminRequest(
          `/rest/v1/${encodeURIComponent(SECURE_DB_TABLES.skins)}?account_id=eq.${encodeURIComponent(accountId)}&skin_id=eq.${encodeURIComponent(skin.skin_id)}`,
          { method:'DELETE', headers:{ Prefer:'return=minimal' } }
        ).catch(() => {});
        throw error;
      }
    }

    return { reused:false, claim, result:skin };
  });
}

function progressionClaimsFromRows(rows) {
  const claimed = new Set();
  const giftSkinClaimed = new Set();
  const metadataByNode = new Map();

  for (const row of Array.isArray(rows) ? rows : []) {
    const nodeId = String(row?.metadata?.nodeId || '');
    if (!nodeId) continue;

    if (
      row.event_type === 'progression_reward'
      ||
      row.event_type === 'progression_skin_roll'
    ) {
      claimed.add(nodeId);
      metadataByNode.set(nodeId,row.metadata || {});
    }

    if (row.event_type === 'progression_gift_skin') {
      giftSkinClaimed.add(nodeId);
    }
  }

  return { claimed, giftSkinClaimed, metadataByNode };
}

function progressionWorldsView(totalXp, claims) {
  const safeXp = Math.max(0, Math.floor(Number(totalXp) || 0));
  const claimed = claims?.claimed || new Set();
  const giftSkinClaimed = claims?.giftSkinClaimed || new Set();

  return PROGRESSION_WORLD_DEFINITIONS.map(world => {
    const unlocked = safeXp >= world.unlockXp;
    const completed = safeXp >= world.endXp;

    const nodes = world.nodes.map(node => {
      const isClaimed = claimed.has(node.id);
      const xpUnlocked = safeXp >= node.xpRequired;
      const status = isClaimed
        ? 'claimed'
        : (xpUnlocked ? 'available' : 'locked');

      return {
        ...node,
        status,
        claimed:isClaimed,
        unlocked:xpUnlocked,
        giftSkinClaimed:
          node.reward?.kind === 'gift'
          ? giftSkinClaimed.has(node.id)
          : false
      };
    });

    return {
      id:world.id,
      index:world.index,
      name:world.name,
      subtitle:world.subtitle,
      theme:world.theme,
      icon:world.icon,
      unlockXp:world.unlockXp,
      endXp:world.endXp,
      unlocked,
      completed,
      nodes
    };
  });
}

async function progressionSkinPool(accountId, allowedRarities = null) {
  if (secureDbReady()) {
    await ensureAuthoritativeShopCatalog().catch(() => false);
  }

  let rows = Object.values(SHOP_SKIN_CATALOG)
    .filter(item =>
      item?.active !== false
      && !COMBO_ONLY_SKIN_IDS.has(String(item.id || ''))
      && (!allowedRarities || allowedRarities.includes(String(item.rarity || '')))
    )
    .map(item => ({
      skin_id:item.id,
      name:item.name,
      rarity:item.rarity,
      limited:false,
      active:true
    }));

  if (!accountId || !secureDbReady()) return rows;

  const ownedRows = await dbSelect(SECURE_DB_TABLES.skins, {
    select:'skin_id',
    account_id:`eq.${accountId}`
  });

  const owned = new Set(ownedRows.map(row => String(row.skin_id || '')));
  return rows.filter(row => !owned.has(String(row.skin_id || '')));
}

function chooseProgressionSkin(pool) {
  const available = Array.isArray(pool) ? pool : [];
  if (!available.length) return null;

  const raritySet = new Set(available.map(item => String(item.rarity || '')));
  const odds = PROGRESSION_SKIN_ODDS.filter(item => raritySet.has(item.rarity));
  const total = odds.reduce((sum,item) => sum + item.weight,0);

  if (!total) {
    return available[crypto.randomInt(0,available.length)];
  }

  let roll = crypto.randomInt(1,total + 1);
  let selectedRarity = odds[odds.length - 1].rarity;

  for (const item of odds) {
    roll -= item.weight;
    if (roll <= 0) {
      selectedRarity = item.rarity;
      break;
    }
  }

  const candidates = available.filter(item => item.rarity === selectedRarity);
  const source = candidates.length ? candidates : available;
  return source[crypto.randomInt(0,source.length)];
}

async function secureProgressionState(accountId = null) {
  if (!accountId) {
    const pool = secureDbReady()
      ? await progressionSkinPool(null)
      : [];

    return {
      previewOnly:true,
      totalXp:0,
      level:1,
      currentXp:0,
      nextLevelXp:500,
      economy:{ gemCoinValue:WILD_GEM_COIN_VALUE },
      odds:progressionOddsPublicView(),
      worlds:progressionWorldsView(0,{claimed:new Set(),giftSkinClaimed:new Set()}),
      rollPool:pool,
      giftPool:pool.filter(item => ['rare','epic'].includes(item.rarity))
    };
  }

  const state = await loadSecureGameState(accountId);
  if (!state?.wallet) return null;

  const [ledgerRows,rollPool,giftPool] = await Promise.all([
    progressionLedgerRows(accountId),
    progressionSkinPool(accountId),
    progressionSkinPool(accountId,['rare','epic'])
  ]);

  const totalXp = totalXpForWallet(state.wallet);
  const claims = progressionClaimsFromRows(ledgerRows);

  return {
    previewOnly:false,
    totalXp,
    level:Number(state.wallet.level || 1),
    currentXp:Number(state.wallet.xp || 0),
    nextLevelXp:serverXpNeeded(Number(state.wallet.level || 1)),
    economy:{ gemCoinValue:WILD_GEM_COIN_VALUE },
    odds:progressionOddsPublicView(),
    worlds:progressionWorldsView(totalXp,claims),
    rollPool,
    giftPool,
    account:secureAccountView(state)
  };
}

function supabaseUrlReady() {
  return /^https:\/\/.+\.supabase\.co$/i.test(SUPABASE_URL);
}

function secureDbReady() {
  /*
     O backend precisa da chave ADMIN/SECRET para gravar contas,
     carteira, skins e recompensas. A publishable é opcional no
     navegador porque o login Google também possui fallback direto.
  */
  return supabaseUrlReady() &&
    SUPABASE_ADMIN_KEY.length > 12;
}

function googleOAuthReady() {
  /*
     Isto significa que o WildSnake possui configuração suficiente
     para iniciar e validar OAuth. O provider Google também precisa
     estar habilitado no painel Authentication > Providers do Supabase.
  */
  return secureDbReady();
}

function supabaseConfigDiagnostics() {
  const missing = [];

  if (!supabaseUrlReady()) {
    missing.push('SUPABASE_URL');
  }

  if (SUPABASE_ADMIN_KEY.length <= 12) {
    missing.push('SUPABASE_SECRET_KEY ou SUPABASE_SERVICE_ROLE_KEY');
  }

  return {
    urlConfigured: supabaseUrlReady(),
    adminKeyConfigured: SUPABASE_ADMIN_KEY.length > 12,
    publishableKeyConfigured: SUPABASE_PUBLISHABLE_KEY.length > 12,
    googleOAuthReady: googleOAuthReady(),
    missing
  };
}

function supabaseAdminHeaders(extra = {}) {
  const headers = {
    apikey: SUPABASE_ADMIN_KEY,
    'Content-Type': 'application/json',
    ...extra
  };

  // Legacy service_role é JWT. A nova sb_secret_* deve ir apenas em apikey.
  if (SUPABASE_ADMIN_KEY.startsWith('eyJ')) {
    headers.Authorization = `Bearer ${SUPABASE_ADMIN_KEY}`;
  }

  return headers;
}

async function supabaseAdminRequest(
  pathname,
  {
    method = 'GET',
    body,
    headers = {}
  } = {}
) {
  if (!secureDbReady()) {
    const error = new Error('SUPABASE_SERVER_NOT_CONFIGURED');
    error.status = 503;
    throw error;
  }

  const response = await fetch(
    `${SUPABASE_URL}${pathname}`,
    {
      method,
      headers: supabaseAdminHeaders(headers),
      body: body === undefined ? undefined : JSON.stringify(body)
    }
  );

  const text = await response.text();
  let data = null;

  if (text) {
    try {
      data = JSON.parse(text);
    } catch {
      data = text;
    }
  }

  if (!response.ok) {
    const error = new Error(
      data?.message ||
      data?.hint ||
      data?.details ||
      String(data || `Supabase HTTP ${response.status}`)
    );
    error.status = response.status;
    error.code = data?.code || null;
    error.data = data;
    throw error;
  }

  return data;
}

function pgQuery(params = {}) {
  const query = new URLSearchParams();
  for (const [key, value] of Object.entries(params)) {
    if (value !== undefined && value !== null) query.set(key, String(value));
  }
  return query.toString();
}

async function dbSelect(table, params = {}) {
  const query = pgQuery(params);
  const data = await supabaseAdminRequest(
    `/rest/v1/${encodeURIComponent(table)}${query ? `?${query}` : ''}`,
    { method: 'GET' }
  );
  return Array.isArray(data) ? data : [];
}

async function dbInsert(table, row, { upsert = false, onConflict = null } = {}) {
  const query = onConflict ? `?on_conflict=${encodeURIComponent(onConflict)}` : '';
  return supabaseAdminRequest(
    `/rest/v1/${encodeURIComponent(table)}${query}`,
    {
      method: 'POST',
      headers: {
        Prefer: upsert
          ? 'resolution=merge-duplicates,return=representation'
          : 'return=representation'
      },
      body: row
    }
  );
}

async function dbUpdate(table, filters, patch) {
  const query = pgQuery(filters);
  return supabaseAdminRequest(
    `/rest/v1/${encodeURIComponent(table)}?${query}`,
    {
      method: 'PATCH',
      headers: { Prefer: 'return=representation' },
      body: patch
    }
  );
}

async function dbRpc(name, payload) {
  return supabaseAdminRequest(
    `/rest/v1/rpc/${encodeURIComponent(name)}`,
    {
      method: 'POST',
      headers: { Prefer: 'return=representation' },
      body: payload
    }
  );
}

async function verifySupabaseUser(accessToken) {
  const token = String(accessToken || '').trim();
  if (!token) return null;

  /*
     A sessão OAuth pertence ao usuário, mas /auth/v1/user precisa
     receber uma API key válida do mesmo projeto Supabase.

     No servidor, priorizamos a Secret/Service Role Key, que nunca é
     enviada ao navegador, e usamos a Publishable Key como fallback.
     Isso evita falsos "Sessão Google/Supabase inválida" quando a
     publishable foi rotacionada ou ficou divergente no Render.
  */
  const apiKeys = [
    SUPABASE_ADMIN_KEY,
    SUPABASE_PUBLISHABLE_KEY
  ].filter((value, index, array) =>
    value && value.length > 12 && array.indexOf(value) === index
  );

  if (!apiKeys.length) {
    console.error('Google auth: nenhuma API key Supabase configurada no servidor.');
    return null;
  }

  for (const apiKey of apiKeys) {
    try {
      const response = await fetch(
        `${SUPABASE_URL}/auth/v1/user`,
        {
          headers: {
            apikey: apiKey,
            Authorization: `Bearer ${token}`
          }
        }
      );

      if (response.ok) {
        const user = await response.json().catch(() => null);
        if (user?.id) return user;
      } else {
        const detail = await response.text().catch(() => '');
        console.warn(
          `Google auth verify falhou HTTP ${response.status}: ${String(detail).slice(0, 180)}`
        );
      }
    } catch (error) {
      console.warn('Google auth verify erro:', error?.message || error);
    }
  }

  return null;
}

function sessionFromToken(token) {
  const value = String(token || '').trim();
  if (!value) return null;

  if(revokedSessionTokens.has(value)){
    return null;
  }

  const cached = sessions.get(value);

  if (cached) {
    if (Date.now() > cached.expiresAt) {
      sessions.delete(value);
      return null;
    }

    return cached;
  }

  const signed = parseSignedSessionToken(value);

  if (!signed) {
    return null;
  }

  sessions.set(value,signed);
  return signed;
}

function cleanEmail(value) {
  return String(value || '').trim().toLowerCase().slice(0, 320);
}

function googleDisplayName(user) {
  const meta = user?.user_metadata || {};
  return cleanDisplayName(
    meta.full_name ||
    meta.name ||
    meta.user_name ||
    cleanEmail(user?.email).split('@')[0] ||
    'Player'
  ) || 'Player';
}

function googleUsernameBase(user) {
  const emailBase = cleanEmail(user?.email).split('@')[0] || 'player';
  const safe = cleanUsername(emailBase).slice(0, 16) || 'player';
  return safe;
}

async function uniqueUsername(base, fallbackId = '') {
  let candidate = cleanUsername(base) || `player_${String(fallbackId).slice(0, 6)}`;
  candidate = candidate.slice(0, MAX_USERNAME_LENGTH);

  for (let attempt = 0; attempt < 8; attempt++) {
    const rows = await dbSelect(SECURE_DB_TABLES.accounts, {
      select: 'id',
      username: `ilike.${candidate}`,
      limit: 1
    });
    if (!rows.length) return candidate;
    const suffix = crypto.randomBytes(2).toString('hex');
    candidate = `${cleanUsername(base).slice(0, 17) || 'player'}_${suffix}`
      .slice(0, MAX_USERNAME_LENGTH);
  }

  return `player_${crypto.randomBytes(5).toString('hex')}`.slice(0, MAX_USERNAME_LENGTH);
}

async function findSecureAccountById(accountId) {
  const rows = await dbSelect(SECURE_DB_TABLES.accounts, {
    select: '*',
    id: `eq.${accountId}`,
    limit: 1
  });
  return rows[0] || null;
}

async function findSecureAccountByUsername(username) {
  const normalized = cleanUsername(username);
  if (!normalized) return null;
  const rows = await dbSelect(SECURE_DB_TABLES.accounts, {
    select: '*',
    username: `ilike.${normalized}`,
    limit: 1
  });
  return rows[0] || null;
}

async function findSecureAccountByGoogleUserId(userId) {
  const rows = await dbSelect(SECURE_DB_TABLES.accounts, {
    select: '*',
    google_user_id: `eq.${userId}`,
    limit: 1
  });
  return rows[0] || null;
}

async function ensureSecureAccountCompanions(accountId) {
  const walletRows = await dbSelect(SECURE_DB_TABLES.wallets, {
    select: 'account_id',
    account_id: `eq.${accountId}`,
    limit: 1
  });
  if (!walletRows.length) {
    await dbInsert(SECURE_DB_TABLES.wallets, {
      account_id: accountId,
      coins: 0,
      wildgems: 0,
      level: 1,
      xp: 0
    }).catch(error => {
      if (error.status !== 409) throw error;
    });
  }

  const basicRows = await dbSelect(SECURE_DB_TABLES.skins, {
    select: 'skin_id',
    account_id: `eq.${accountId}`,
    skin_id: 'eq.basic',
    limit: 1
  });
  if (!basicRows.length) {
    await dbInsert(SECURE_DB_TABLES.skins, {
      account_id: accountId,
      skin_id: 'basic',
      source: 'starter'
    }).catch(error => {
      if (error.status !== 409) throw error;
    });
  }
}

async function loadSecureGameState(accountId) {
  const account = await findSecureAccountById(accountId);
  if (!account) return null;

  await ensureSecureAccountCompanions(accountId);

  const [walletRows, skinRows] = await Promise.all([
    dbSelect(SECURE_DB_TABLES.wallets, {
      select: '*',
      account_id: `eq.${accountId}`,
      limit: 1
    }),
    dbSelect(SECURE_DB_TABLES.skins, {
      select: 'skin_id,source,acquired_at',
      account_id: `eq.${accountId}`,
      order: 'acquired_at.asc'
    })
  ]);

  const wallet = walletRows[0] || {
    coins: 0,
    wildgems: 0,
    level: 1,
    xp: 0,
    total_matches: 0,
    total_kills: 0,
    total_score: 0
  };

  const ownedSkins = skinRows.map(row => row.skin_id);
  if (!ownedSkins.includes('basic')) ownedSkins.unshift('basic');

  return {
    account,
    wallet,
    ownedSkins
  };
}


function tutorialStatusForAccount(account) {
  if (!account) return 'pending';

  if (String(account.reward_state || '').toLowerCase() === 'skipped') {
    return 'skipped';
  }

  if (account.tutorial_completed) {
    return 'completed';
  }

  return 'pending';
}

function tutorialIsRequired(account) {
  return tutorialStatusForAccount(account) === 'pending';
}

function secureAccountView(state) {
  if (!state?.account) return null;
  const { account, wallet, ownedSkins } = state;
  return {
    id: account.id,
    username: account.username || 'player',
    displayName: account.display_name || 'Player',
    createdAt: account.created_at,
    role: account.role || 'player',
    provider: account.provider || 'local',
    email: account.google_email || null,
    googleLinked: !!account.google_user_id,
    tutorialCompleted: tutorialStatusForAccount(account) === 'completed',
    tutorialRequired: tutorialIsRequired(account),
    tutorialStatus: tutorialStatusForAccount(account),
    tutorialBonusClaimed:
      tutorialStatusForAccount(account) === 'completed'
      && String(account.reward_state || '').toLowerCase() !== 'skipped',
    rewardState: account.reward_state || 'none',
    equippedSkin: account.equipped_skin || 'basic',
    coins: Number(wallet?.coins || 0),
    gems: Number(wallet?.wildgems || 0),
    level: Number(wallet?.level || 1),
    xp: Number(wallet?.xp || 0),
    totalMatches: Number(wallet?.total_matches || 0),
    totalKills: Number(wallet?.total_kills || 0),
    totalScore: Number(wallet?.total_score || 0),
    ownedSkins: Array.isArray(ownedSkins) ? ownedSkins : ['basic'],
    ownedCombos:
      Array.isArray(ownedSkins)
        ? Object.values(SHOP_COMBOS)
            .filter(combo => combo.skins.every(skinId => ownedSkins.includes(skinId)))
            .map(combo => combo.id)
        : []
  };
}

async function createSecureLocalAccount({ username, password, displayName }) {
  const normalized = cleanUsername(username);

  if (normalized.length < 3) {
    return { ok: false, status: 400, error: 'O usuário precisa ter pelo menos 3 caracteres.' };
  }

  if (!passwordLooksValid(password)) {
    return {
      ok: false,
      status: 400,
      error: `A senha precisa ter pelo menos ${MIN_PASSWORD_LENGTH} caracteres.`
    };
  }

  if (await findSecureAccountByUsername(normalized)) {
    return { ok: false, status: 409, error: 'Este nome de usuário já existe.' };
  }

  const salt = crypto.randomBytes(16).toString('hex');
  const passwordHash = await scryptHash(password, salt);
  const accountId = crypto.randomUUID();

  try {
    await dbInsert(SECURE_DB_TABLES.accounts, {
      id: accountId,
      username: normalized,
      display_name: cleanDisplayName(displayName) || normalized,
      password_salt: salt,
      password_hash: passwordHash,
      provider: 'local',
      role: 'player',
      equipped_skin: 'basic',
      tutorial_completed: false,
      reward_state: 'none'
    });

    await ensureSecureAccountCompanions(accountId);
    const state = await loadSecureGameState(accountId);
    const token = createSession(accountId, 'player');
    activateAccountSession(accountId, token);

    return {
      ok: true,
      status: 200,
      token,
      isNew: true,
      tutorialRequired: true,
      account: secureAccountView(state)
    };
  } catch (error) {
    try {
      await supabaseAdminRequest(
        `/rest/v1/${SECURE_DB_TABLES.accounts}?id=eq.${encodeURIComponent(accountId)}`,
        { method: 'DELETE', headers: { Prefer: 'return=minimal' } }
      );
    } catch {}
    throw error;
  }
}


async function createQrGuestAccount() {
  if (!secureDbReady()) {
    return {
      ok:false,
      status:503,
      code:'SECURE_DB_NOT_READY',
      error:'O servidor de contas ainda não está pronto.'
    };
  }

  const suffix = crypto.randomBytes(4).toString('hex');
  const username = await uniqueUsername(`qr_${suffix}`);
  const password = crypto.randomBytes(24).toString('base64url');
  const displayName = `Player ${crypto.randomInt(1000, 10000)}`;

  const result = await createSecureLocalAccount({
    username,
    password,
    displayName
  });

  if (!result?.ok) {
    return result;
  }

  try {
    await dbUpdate(
      SECURE_DB_TABLES.accounts,
      { id:`eq.${result.account?.id}` },
      { provider:'qr_guest' }
    );

    const state = await loadSecureGameState(result.account?.id);

    return {
      ...result,
      autoCreated:true,
      recoverableByGoogle:true,
      account:secureAccountView(state)
    };
  } catch (error) {
    console.error('qr guest provider update:', error?.message || error);

    return {
      ...result,
      autoCreated:true,
      recoverableByGoogle:true
    };
  }
}


async function loginSecureLocalAccount({ username, password }) {
  const normalized = cleanUsername(username);
  let account = await findSecureAccountByUsername(normalized);

  /*
     Migração automática das contas LOCAIS da versão antiga.
     O arquivo legado guardava apenas identidade + hash da senha; portanto
     preservamos a conta e a senha sem transformar dados de localStorage
     (saldo/skins do navegador) em saldo confiável no servidor.
     Conta antiga é marcada como tutorial concluído para não ganhar prêmio
     de primeiro acesso de novo.
  */
  if (!account) {
    const legacy = Object.values(persistentState.accounts || {})
      .find(item => cleanUsername(item?.username) === normalized);

    if (legacy?.salt && legacy?.passwordHash) {
      const legacyCandidate = await scryptHash(String(password || ''), legacy.salt);

      if (safeEqualHex(legacyCandidate, legacy.passwordHash)) {
        const migratedId = crypto.randomUUID();
        try {
          const rows = await dbInsert(SECURE_DB_TABLES.accounts, {
            id: migratedId,
            username: normalized,
            display_name: cleanDisplayName(legacy.displayName) || normalized,
            password_salt: legacy.salt,
            password_hash: legacy.passwordHash,
            provider: 'local',
            role: legacy.role || 'player',
            equipped_skin: 'basic',
            tutorial_completed: true,
            tutorial_completed_at: new Date().toISOString(),
            reward_state: 'none',
            created_at: legacy.createdAt || new Date().toISOString(),
            last_login_at: new Date().toISOString()
          });
          account = rows?.[0] || await findSecureAccountByUsername(normalized);
          if (account?.id) await ensureSecureAccountCompanions(account.id);
        } catch (error) {
          // Corrida de migração: outra requisição pode ter criado a mesma conta.
          account = await findSecureAccountByUsername(normalized);
          if (!account) throw error;
        }
      }
    }
  }

  if (!account || !account.password_salt || !account.password_hash) {
    return { ok: false, status: 401, error: 'Usuário ou senha inválidos.' };
  }

  const candidate = await scryptHash(String(password || ''), account.password_salt);
  if (!safeEqualHex(candidate, account.password_hash)) {
    return { ok: false, status: 401, error: 'Usuário ou senha inválidos.' };
  }

  const currentActiveSession =
    getActiveAccountSession(account.id);

  if(currentActiveSession){
    const transfer =
      createSessionTransferRequest(account.id);

    return {
      ok:false,
      status:409,
      code:'ACCOUNT_ALREADY_ACTIVE',
      requestId:transfer.requestId,
      expiresAt:transfer.expiresAt,
      error:'Esta conta já está conectada em outro navegador. Enviamos uma solicitação para o navegador que está usando a conta.'
    };
  }

  await dbUpdate(
    SECURE_DB_TABLES.accounts,
    { id: `eq.${account.id}` },
    { last_login_at: new Date().toISOString() }
  );

  const state = await loadSecureGameState(account.id);
  const token = createSession(account.id, account.role || 'player');
  activateAccountSession(account.id, token);

  return {
    ok: true,
    status: 200,
    token,
    isNew: false,
    tutorialRequired: tutorialIsRequired(state.account),
    account: secureAccountView(state)
  };
}

async function createGoogleGameAccount(user) {
  const username = await uniqueUsername(googleUsernameBase(user), user.id);
  const rows = await dbInsert(SECURE_DB_TABLES.accounts, {
    id: crypto.randomUUID(),
    username,
    display_name: googleDisplayName(user),
    google_user_id: user.id,
    google_email: cleanEmail(user.email) || null,
    provider: 'google',
    role: 'player',
    equipped_skin: 'basic',
    tutorial_completed: false,
    reward_state: 'none'
  });

  const account = rows?.[0];
  if (!account?.id) throw new Error('Falha ao criar conta Google no WildSnake.');
  await ensureSecureAccountCompanions(account.id);
  return account;
}

async function resolveGoogleGameAccount(user, intent = 'login') {
  let account = await findSecureAccountByGoogleUserId(user.id);
  let isNew = false;

  if (!account && intent !== 'create') {
    return {
      ok: false,
      status: 404,
      code: 'GOOGLE_ACCOUNT_NOT_REGISTERED',
      error: 'Não existe uma conta WildSnake cadastrada com este Google.'
    };
  }

  if (!account) {
    account = await createGoogleGameAccount(user);
    isNew = true;
  } else {
    await dbUpdate(
      SECURE_DB_TABLES.accounts,
      { id: `eq.${account.id}` },
      {
        google_email: cleanEmail(user.email) || account.google_email || null,
        last_login_at: new Date().toISOString()
      }
    );
  }

  const state = await loadSecureGameState(account.id);

  const currentActiveSession =
    getActiveAccountSession(account.id);

  if(currentActiveSession){
    const transfer =
      createSessionTransferRequest(account.id);

    return {
      ok:false,
      status:409,
      code:'ACCOUNT_ALREADY_ACTIVE',
      requestId:transfer.requestId,
      expiresAt:transfer.expiresAt,
      error:'Esta conta já está conectada em outro navegador.'
    };
  }

  const token = createSession(account.id, account.role || 'player');
  activateAccountSession(account.id, token);

  return {
    ok: true,
    status: 200,
    token,
    isNew,
    tutorialRequired: tutorialIsRequired(state.account),
    account: secureAccountView(state)
  };
}

async function linkGoogleToSecureAccount(accountId, user) {
  const account = await findSecureAccountById(accountId);
  if (!account) {
    return { ok: false, status: 404, error: 'Conta WildSnake não encontrada.' };
  }

  if (account.google_user_id === user.id) {
    const state = await loadSecureGameState(account.id);
    return { ok: true, account: secureAccountView(state), alreadyLinked: true };
  }

  const owner = await findSecureAccountByGoogleUserId(user.id);
  if (owner && owner.id !== account.id) {
    return {
      ok: false,
      status: 409,
      code: 'GOOGLE_ALREADY_LINKED',
      error: 'Este Google já está vinculado a outra conta WildSnake.'
    };
  }

  const provider = account.provider === 'google' ? 'google' : 'local+google';
  await dbUpdate(
    SECURE_DB_TABLES.accounts,
    { id: `eq.${account.id}` },
    {
      google_user_id: user.id,
      google_email: cleanEmail(user.email) || null,
      provider,
      updated_at: new Date().toISOString()
    }
  );

  const state = await loadSecureGameState(account.id);
  return { ok: true, account: secureAccountView(state), alreadyLinked: false };
}

async function secureAccountStateFromRequest(req) {
  const session = sessionFromRequest(req);
  if (!session) return null;
  return loadSecureGameState(session.accountId);
}

function randomRewardTypeForCard(cardIndex) {
  const deck = ['coins', 'gems', 'skin'];
  // Fisher-Yates usando crypto. A escolha da carta realmente participa do sorteio.
  for (let i = deck.length - 1; i > 0; i--) {
    const j = crypto.randomInt(0, i + 1);
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck[clamp(Number(cardIndex) || 0, 0, 2)];
}

function chooseWeightedTutorialRarity() {
  const total = TUTORIAL_SKIN_ODDS.reduce((sum, item) => sum + item.weight, 0);
  let roll = crypto.randomInt(1, total + 1);
  for (const item of TUTORIAL_SKIN_ODDS) {
    roll -= item.weight;
    if (roll <= 0) return item;
  }
  return TUTORIAL_SKIN_ODDS[TUTORIAL_SKIN_ODDS.length - 1];
}

async function selectTutorialReward(accountId, cardIndex) {
  const state = await loadSecureGameState(accountId);
  if (!state) return { ok: false, status: 404, error: 'Conta não encontrada.' };

  if (tutorialStatusForAccount(state.account) === 'skipped') {
    return {
      ok: false,
      status: 409,
      code: 'TUTORIAL_SKIPPED',
      error: 'Este tutorial foi pulado nesta conta e não pode mais gerar bônus.'
    };
  }

  if (tutorialStatusForAccount(state.account) === 'completed') {
    return {
      ok: false,
      status: 409,
      code: 'TUTORIAL_ALREADY_COMPLETED',
      error: 'Este tutorial já foi concluído nesta conta.'
    };
  }

  if (state.account.reward_state === 'generated' && state.account.reward_payload) {
    return { ok: true, reward: state.account.reward_payload, reused: true };
  }

  const index = clamp(Math.floor(Number(cardIndex) || 0), 0, 2);
  const type = randomRewardTypeForCard(index);
  let reward;

  if (type === 'coins') {
    reward = {
      type: 'coins',
      amount: crypto.randomInt(1000, 20001),
      cardIndex: index
    };
  } else if (type === 'gems') {
    reward = {
      type: 'gems',
      amount: crypto.randomInt(100, 301),
      cardIndex: index
    };
  } else {
    reward = {
      type: 'skin',
      cardIndex: index,
      awaitingRoll: true,
      odds: TUTORIAL_SKIN_ODDS
    };
  }

  await dbUpdate(
    SECURE_DB_TABLES.accounts,
    { id: `eq.${accountId}`, reward_state: 'eq.none', tutorial_completed: 'eq.false' },
    {
      reward_state: 'generated',
      reward_payload: reward,
      reward_generated_at: new Date().toISOString(),
      tutorial_started_at: state.account.tutorial_started_at || new Date().toISOString()
    }
  );

  const updated = await findSecureAccountById(accountId);
  return { ok: true, reward: updated?.reward_payload || reward, reused: false };
}

async function rollTutorialSkin(accountId) {
  const state = await loadSecureGameState(accountId);
  if (!state) return { ok: false, status: 404, error: 'Conta não encontrada.' };

  const reward = state.account.reward_payload;
  if (state.account.reward_state !== 'generated' || reward?.type !== 'skin') {
    return { ok: false, status: 409, error: 'Não existe uma roleta de skin pendente.' };
  }

  if (reward.skinId) {
    return { ok: true, reward, reused: true };
  }

  const rarity = chooseWeightedTutorialRarity();
  let candidates = await dbSelect(SECURE_DB_TABLES.catalog, {
    select: 'skin_id,name,rarity,limited',
    active: 'eq.true',
    rarity: `eq.${rarity.rarity}`,
    skin_id: 'neq.basic'
  });

  if (!candidates.length) {
    candidates = await dbSelect(SECURE_DB_TABLES.catalog, {
      select: 'skin_id,name,rarity,limited',
      active: 'eq.true',
      skin_id: 'neq.basic'
    });
  }

  if (!candidates.length) {
    return { ok: false, status: 503, error: 'Catálogo de skins indisponível.' };
  }

  const chosen = candidates[crypto.randomInt(0, candidates.length)];

  // A função SQL trava a linha da conta. Se duas abas chamarem a roleta
  // ao mesmo tempo, só o primeiro resultado é gravado e ambos recebem
  // exatamente a mesma skin. A animação do cliente nunca decide o prêmio.
  const finalReward = await dbRpc('ws_set_tutorial_skin', {
    p_account_id: accountId,
    p_skin_id: chosen.skin_id,
    p_skin_name: chosen.name,
    p_rarity: chosen.rarity,
    p_rare_protection: chosen.rarity === 'limited'
  });

  return { ok: true, reward: finalReward, reused: false };
}

function tutorialOddsPublicView() {
  return TUTORIAL_SKIN_ODDS.map(item => ({
    rarity: item.rarity,
    label: item.label,
    percent: item.weight
  }));
}

async function listLimitedInventorySecure() {
  if (!secureDbReady()) return limitedCatalogView();
  const rows = await dbSelect('limited_skin_inventory', {
    select: 'skin_id,name,stock,stock_max,price_wildgems,active',
    active: 'eq.true',
    order: 'price_wildgems.asc'
  });
  return rows.map(row => ({
    id: row.skin_id,
    name: row.name,
    currency: 'gem',
    price: Number(row.price_wildgems || 0),
    stock: Number(row.stock || 0),
    stockMax: Number(row.stock_max || 0)
  }));
}

function secureErrorMessage(error) {
  const raw = String(error?.message || error || '');
  if (raw.includes('COINS_INSUFICIENTES')) return '🪙 WildCoins insuficientes.';
  if (raw.includes('GEMS_INSUFICIENTES')) return '💎 WildGems insuficientes.';
  if (raw.includes('ESGOTADA')) return 'Edição limitada esgotada.';
  if (raw.includes('SKIN_JA_POSSUI')) return 'Você já possui esta skin.';
  if (raw.includes('SKIN_INVALIDA')) return 'Skin inválida.';
  if (raw.includes('RECOMPENSA_NAO_GERADA')) return 'A recompensa ainda não foi gerada.';
  if (raw.includes('CARTEIRA_NAO_ENCONTRADA')) return 'Carteira da conta não encontrada.';
  if (raw.includes('MATCH_REWARD_FAILED')) return 'Não foi possível creditar a recompensa da partida.';
  if (raw.includes('COMBO_JA_POSSUI')) return 'Você já possui este combo.';
  if (raw.includes('COMBO_INVALIDO')) return 'Combo ou forma de pagamento inválida.';
  if (raw.includes('COMBO_INVALIDO')) return 'Combo inválido.';
  if (raw.includes('RECOMPENSA_JA_RESGATADA')) return 'Esta recompensa já foi resgatada.';
  if (raw.includes('XP_INSUFICIENTE')) return 'Você ainda não possui XP suficiente.';
  if (raw.includes('PRESENTE_NAO_RESGATADO')) return 'Abra o presente antes de escolher a skin.';
  if (raw.includes('ACCOUNT_REQUIRED')) return 'Entre na sua conta para receber esta recompensa.';
  if (raw.includes('RECOMPENSA_INVALIDA')) return 'Recompensa inválida.';
  if (raw.includes('SKIN_FORA_DA_FAIXA')) return 'Esta skin não pode ser escolhida neste presente.';
  if (raw.includes('SUPABASE_SERVER_NOT_CONFIGURED')) {
    return 'Servidor seguro ainda não está conectado ao Supabase.';
  }
  return 'Não foi possível concluir esta operação.';
}

async function secureSkinForAccount(accountId, requestedSkin) {
  if (!accountId || !secureDbReady()) return 'basic';
  const skin = sanitizeSkin(requestedSkin);
  const rows = await dbSelect(SECURE_DB_TABLES.skins, {
    select: 'skin_id',
    account_id: `eq.${accountId}`,
    skin_id: `eq.${skin}`,
    limit: 1
  });
  return rows.length ? skin : 'basic';
}


/* =========================================================
   V13.10.3 - RECOMPENSA POR COMIDAS AUTORITATIVA NO SERVIDOR
   - O navegador NÃO decide quantas WildCoins recebe.
   - A recompensa depende apenas da quantidade de comidas coletadas.
   - Regra: a cada 3 comidas = 1 WildCoin.
   - Exemplo: 600 comidas = 200 WildCoins.
   - A posição no ranking NÃO altera a recompensa.
   - O ranking usa quem comeu mais.
   - Ledger + matchId reduzem risco de crédito duplicado.
========================================================= */

const MATCH_FOODS_PER_COIN = 3;
const MATCH_MAX_FOOD_COUNT = 10_000_000;
const MATCH_MAX_COINS = Math.floor(
  MATCH_MAX_FOOD_COUNT / MATCH_FOODS_PER_COIN
);

const matchRewardLocks = new Map();
const settledMatchIds = new Set();

function serverXpNeeded(level) {
  const safeLevel = Math.max(1, Math.floor(Number(level) || 1));
  return 500 + (safeLevel - 1) * 250;
}

function foodCoinsFor(foodEaten) {
  const foods = clamp(
    Math.floor(Number(foodEaten) || 0),
    0,
    MATCH_MAX_FOOD_COUNT
  );

  return clamp(
    Math.floor(foods / MATCH_FOODS_PER_COIN),
    0,
    MATCH_MAX_COINS
  );
}

function buildServerMatchRewardPreview(room, snake) {
  const timeMs = Math.max(0, Date.now() - (snake.startedAt || Date.now()));
  const elapsedSeconds = timeMs / 1000;
  const score = Math.max(0, Math.floor(Number(snake.score) || 0));
  const kills = Math.max(0, Math.floor(Number(snake.kills) || 0));
  const foodEaten = clamp(
    Math.floor(Number(snake.foodEaten) || 0),
    0,
    MATCH_MAX_FOOD_COUNT
  );

  const foodCoins = foodCoinsFor(foodEaten);

  const xp = Math.max(
    10,
    Math.floor(
      score * 0.85
      + kills * 60
      + elapsedSeconds * 1.4
    )
  );

  return {
    matchId: snake.matchId || null,
    foodEaten,
    foodCoins,
    coins: foodCoins,
    xp,
    gems: 0,
    levelUps: 0,
    score,
    kills,
    timeMs,
    roomId: room.code,
    roomType: room.type,
    botAssisted: room.type === 'public' && room.botIds.size > 0,
    humansInRoom: room.players.size,
    botsInRoom: room.botIds.size
  };
}

function applyServerXpProgress(wallet, xpAward) {
  let level = Math.max(1, Math.floor(Number(wallet?.level) || 1));
  let xp = Math.max(0, Math.floor(Number(wallet?.xp) || 0));
  let gemsBonus = 0;
  let levelUps = 0;

  xp += Math.max(0, Math.floor(Number(xpAward) || 0));

  while (xp >= serverXpNeeded(level)) {
    xp -= serverXpNeeded(level);
    level += 1;
    levelUps += 1;

    /*
      WildCoins NÃO são mais bônus de nível.
      Elas vêm exclusivamente das comidas coletadas.
      WildGems de marco de nível continuam separadas.
    */
    if (level % 10 === 0) {
      gemsBonus += 2;
    }

    if (levelUps > 250) break;
  }

  return {
    level,
    xp,
    gemsBonus,
    levelUps
  };
}

async function withMatchRewardLock(accountId, task) {
  const previous = matchRewardLocks.get(accountId) || Promise.resolve();
  const current = previous.catch(() => {}).then(task);

  matchRewardLocks.set(accountId, current);

  try {
    return await current;
  } finally {
    if (matchRewardLocks.get(accountId) === current) {
      matchRewardLocks.delete(accountId);
    }
  }
}


async function purchaseShopSkinForAccount(accountId, requestedSkinId) {
  const skinId = sanitizeSkin(requestedSkinId);
  const skin = SHOP_SKIN_CATALOG[skinId];

  if (!skin || skin.active === false || COMBO_ONLY_SKIN_IDS.has(skinId)) {
    throw new Error('SKIN_INVALIDA');
  }

  if (!secureDbReady()) {
    throw new Error('SUPABASE_SERVER_NOT_CONFIGURED');
  }

  return withMatchRewardLock(accountId, async () => {
    await ensureAuthoritativeShopCatalog();

    const state = await loadSecureGameState(accountId);
    if (!state?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const owned = new Set(Array.isArray(state.ownedSkins) ? state.ownedSkins : []);
    if (owned.has(skinId)) throw new Error('SKIN_JA_POSSUI');

    const wallet = state.wallet;
    const price = Math.max(0, Math.floor(Number(skin.price) || 0));
    const currency = skin.currency === 'gem' ? 'gem' : 'coin';
    const oldCoins = Math.max(0, Number(wallet.coins || 0));
    const oldGems = Math.max(0, Number(wallet.wildgems || 0));

    if (!price) throw new Error('SKIN_INVALIDA');
    if (currency === 'coin' && oldCoins < price) throw new Error('COINS_INSUFICIENTES');
    if (currency === 'gem' && oldGems < price) throw new Error('GEMS_INSUFICIENTES');

    const walletPatch = {
      updated_at:new Date().toISOString()
    };

    if (currency === 'coin') walletPatch.coins = oldCoins - price;
    else walletPatch.wildgems = oldGems - price;

    await dbUpdate(
      SECURE_DB_TABLES.wallets,
      { account_id:`eq.${accountId}` },
      walletPatch
    );

    try {
      await dbInsert(SECURE_DB_TABLES.skins, {
        account_id:accountId,
        skin_id:skinId,
        source:'shop'
      });
    } catch (error) {
      // Reverte o débito caso outra instância tenha comprado a mesma skin
      // no mesmo instante ou caso o INSERT falhe por qualquer motivo.
      await dbUpdate(
        SECURE_DB_TABLES.wallets,
        { account_id:`eq.${accountId}` },
        {
          coins:oldCoins,
          wildgems:oldGems,
          updated_at:new Date().toISOString()
        }
      ).catch(() => {});

      if (error?.status === 409) throw new Error('SKIN_JA_POSSUI');
      throw error;
    }

    try {
      await dbInsert(SECURE_DB_TABLES.ledger, {
        account_id:accountId,
        event_type:'skin_purchase',
        currency,
        amount:-price,
        skin_id:skinId,
        idempotency_key:`skin-purchase:${accountId}:${skinId}`,
        metadata:{
          skinId,
          name:skin.name,
          rarity:skin.rarity,
          price,
          currency,
          gemCoinValue:WILD_GEM_COIN_VALUE,
          purchasedAt:new Date().toISOString()
        }
      });
    } catch (error) {
      // A posse + débito já são a fonte de verdade. Ledger é auditoria.
      if (error?.status !== 409) {
        console.error('skin purchase ledger:', error?.message || error);
      }
    }

    const updatedState = await loadSecureGameState(accountId);
    return {
      skin:{ ...skin },
      account:secureAccountView(updatedState)
    };
  });
}


async function deleteOwnedSkinRows(accountId, skinIds) {
  if (!skinIds.length) return;
  const encoded = skinIds.map(id => `"${String(id).replace(/"/g,'')}"`).join(',');
  await supabaseAdminRequest(
    `/rest/v1/${encodeURIComponent(SECURE_DB_TABLES.skins)}?account_id=eq.${encodeURIComponent(accountId)}&skin_id=in.(${encoded})`,
    { method:'DELETE' }
  );
}

async function purchaseShopComboForAccount(accountId, requestedComboId, requestedCurrency) {
  const comboId = String(requestedComboId || '').trim();
  const currency = String(requestedCurrency || '').trim().toLowerCase();
  const combo = SHOP_COMBOS[comboId];

  if (!combo || !['coin','gem'].includes(currency)) {
    throw new Error('COMBO_INVALIDO');
  }

  if (!secureDbReady()) {
    throw new Error('SUPABASE_SERVER_NOT_CONFIGURED');
  }

  return withMatchRewardLock(accountId, async () => {
    await ensureAuthoritativeShopCatalog();

    const state = await loadSecureGameState(accountId);
    if (!state?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const owned = new Set(Array.isArray(state.ownedSkins) ? state.ownedSkins : []);
    if (combo.skins.every(id => owned.has(id))) {
      throw new Error('COMBO_JA_POSSUI');
    }

    const price = currency === 'gem' ? combo.gemPrice : combo.coinPrice;
    const oldCoins = Math.max(0, Number(state.wallet.coins || 0));
    const oldGems = Math.max(0, Number(state.wallet.wildgems || 0));

    if (currency === 'coin' && oldCoins < price) throw new Error('COINS_INSUFICIENTES');
    if (currency === 'gem' && oldGems < price) throw new Error('GEMS_INSUFICIENTES');

    const newSkinIds = combo.skins.filter(id => !owned.has(id));

    const walletPatch = { updated_at:new Date().toISOString() };
    if (currency === 'coin') walletPatch.coins = oldCoins - price;
    else walletPatch.wildgems = oldGems - price;

    await dbUpdate(
      SECURE_DB_TABLES.wallets,
      { account_id:`eq.${accountId}` },
      walletPatch
    );

    const inserted = [];

    try {
      for (const skinId of newSkinIds) {
        await dbInsert(
          SECURE_DB_TABLES.skins,
          {
            account_id:accountId,
            skin_id:skinId,
            source:`combo:${comboId}`
          },
          { upsert:true, onConflict:'account_id,skin_id' }
        );
        inserted.push(skinId);
      }
    } catch (error) {
      await dbUpdate(
        SECURE_DB_TABLES.wallets,
        { account_id:`eq.${accountId}` },
        {
          coins:oldCoins,
          wildgems:oldGems,
          updated_at:new Date().toISOString()
        }
      ).catch(()=>{});

      await deleteOwnedSkinRows(accountId, inserted).catch(()=>{});
      throw error;
    }

    try {
      await dbInsert(SECURE_DB_TABLES.ledger, {
        account_id:accountId,
        event_type:'combo_purchase',
        currency,
        amount:-price,
        skin_id:null,
        idempotency_key:`combo-purchase:${accountId}:${comboId}`,
        metadata:{
          comboId,
          comboName:combo.name,
          skins:[...combo.skins],
          currency,
          price,
          purchasedAt:new Date().toISOString()
        }
      });
    } catch (error) {
      if (error?.status !== 409) {
        console.error('combo purchase ledger:', error?.message || error);
      }
    }

    const updated = await loadSecureGameState(accountId);

    return {
      combo:{
        id:combo.id,
        name:combo.name,
        currency,
        price,
        skins:[...combo.skins]
      },
      account:secureAccountView(updated)
    };
  });
}

async function grantSecureMatchReward(snake, rewardPreview) {
  const accountId = snake?.accountId;
  const matchId = rewardPreview?.matchId || snake?.matchId;

  if (!accountId) {
    return {
      ok: false,
      code: 'ACCOUNT_REQUIRED',
      error: 'Entre em uma conta WildSnake para receber recompensas.'
    };
  }

  if (!matchId) {
    return {
      ok: false,
      code: 'MATCH_ID_MISSING',
      error: 'A partida não possui identificador de recompensa.'
    };
  }

  if (!secureDbReady()) {
    return {
      ok: false,
      code: 'SECURE_BACKEND_UNAVAILABLE',
      error: 'Servidor seguro de recompensas indisponível no momento.'
    };
  }

  return withMatchRewardLock(accountId, async () => {
    const idempotencyKey = `match:${accountId}:${matchId}`;

    const existing = await dbSelect(
      SECURE_DB_TABLES.ledger,
      {
        select: 'id,amount,metadata,created_at',
        idempotency_key: `eq.${idempotencyKey}`,
        limit: 1
      }
    );

    if (existing.length) {
      const state = await loadSecureGameState(accountId);
      const metadata = existing[0]?.metadata || {};

      return {
        ok: true,
        alreadyGranted: true,
        reward: {
          ...rewardPreview,
          ...metadata,
          coins: Number(
            existing[0]?.amount
            ?? metadata?.coins
            ?? rewardPreview?.coins
            ?? 0
          )
        },
        account: secureAccountView(state)
      };
    }

    if (settledMatchIds.has(idempotencyKey)) {
      const state = await loadSecureGameState(accountId);
      return {
        ok: true,
        alreadyGranted: true,
        reward: rewardPreview,
        account: secureAccountView(state)
      };
    }

    const state = await loadSecureGameState(accountId);

    if (!state?.wallet) {
      throw new Error('CARTEIRA_NAO_ENCONTRADA');
    }

    const wallet = state.wallet;
    const progress = applyServerXpProgress(wallet, rewardPreview.xp);

    const foodEaten = clamp(
      Math.floor(Number(rewardPreview.foodEaten) || 0),
      0,
      MATCH_MAX_FOOD_COUNT
    );

    const foodCoins = foodCoinsFor(foodEaten);
    const totalCoinsAwarded = foodCoins;
    const gemsAwarded = Math.max(0, progress.gemsBonus);

    const currentCoins = Math.max(0, Number(wallet.coins || 0));
    const currentGems = Math.max(0, Number(wallet.wildgems || 0));
    const currentMatches = Math.max(0, Number(wallet.total_matches || 0));
    const currentKills = Math.max(0, Number(wallet.total_kills || 0));
    const currentScore = Math.max(0, Number(wallet.total_score || 0));

    const finalReward = {
      ...rewardPreview,
      foodEaten,
      foodCoins,
      coins: totalCoinsAwarded,
      xp: Math.max(0, Math.floor(Number(rewardPreview.xp) || 0)),
      gems: gemsAwarded,
      levelUps: progress.levelUps
    };

    await dbUpdate(
      SECURE_DB_TABLES.wallets,
      { account_id: `eq.${accountId}` },
      {
        coins: currentCoins + totalCoinsAwarded,
        wildgems: currentGems + gemsAwarded,
        level: progress.level,
        xp: progress.xp,
        total_matches: currentMatches + 1,
        total_kills: currentKills + Math.max(0, Number(rewardPreview.kills || 0)),
        total_score: currentScore + Math.max(0, Number(rewardPreview.score || 0)),
        updated_at: new Date().toISOString()
      }
    );

    try {
      await dbInsert(
        SECURE_DB_TABLES.ledger,
        {
          account_id: accountId,
          event_type: 'match_reward',
          currency: 'coin',
          amount: totalCoinsAwarded,
          idempotency_key: idempotencyKey,
          metadata: {
            ...finalReward,
            creditedAt: new Date().toISOString()
          }
        }
      );
    } catch (error) {
      if (error?.status !== 409) {
        console.error('match reward ledger:', error);
      }
    }

    settledMatchIds.add(idempotencyKey);

    if (settledMatchIds.size > 20000) {
      const first = settledMatchIds.values().next().value;
      if (first) settledMatchIds.delete(first);
    }

    const updatedState = await loadSecureGameState(accountId);

    return {
      ok: true,
      alreadyGranted: false,
      reward: finalReward,
      account: secureAccountView(updatedState)
    };
  });
}

function emitMatchRewardResult(socket, result, matchId) {
  if (!socket) return;

  if (result?.ok) {
    socket.emit('matchRewardGranted', {
      ok: true,
      matchId,
      alreadyGranted: !!result.alreadyGranted,
      reward: result.reward,
      account: result.account,
      version: GAME_VERSION
    });
    return;
  }

  socket.emit('matchRewardError', {
    ok: false,
    matchId,
    code: result?.code || 'MATCH_REWARD_FAILED',
    error: result?.error || 'Não foi possível creditar a recompensa da partida.',
    version: GAME_VERSION
  });
}

function socketEventAllowed(socket, eventName, max, windowMs) {
  const now = Date.now();
  if (!socket.data.wsRateBuckets) socket.data.wsRateBuckets = new Map();
  const key = String(eventName);
  let bucket = socket.data.wsRateBuckets.get(key);

  if (!bucket || now - bucket.startedAt > windowMs) {
    bucket = { startedAt: now, count: 0 };
    socket.data.wsRateBuckets.set(key, bucket);
  }

  bucket.count++;
  return bucket.count <= max;
}


/* =========================================================
   V13 - PERFIL DE DESEMPENHO / REDE ADAPTATIVA
========================================================= */

const NETWORK_PROFILES = {

  weak:{
    id:'weak',
    worldHz:6,
    segmentLimit:24,
    foodHz:1,
    interpolationHint:0.18
  },

  medium:{
    id:'medium',
    worldHz:8,
    segmentLimit:34,
    foodHz:2,
    interpolationHint:0.13
  },

  strong:{
    id:'strong',
    worldHz:10,
    segmentLimit:48,
    foodHz:2,
    interpolationHint:0.10
  }

};


function normalizePerformanceTier(
  value
){

  const tier =
    String(
      value
      ||
      'medium'
    )
    .toLowerCase();

  if(
    NETWORK_PROFILES[
      tier
    ]
  ){

    return tier;

  }

  return 'medium';

}


function networkProfileForPlayer(
  player,
  room = null
){

  const base = NETWORK_PROFILES[
    normalizePerformanceTier(
      player.performanceTier
    )
  ];

  if (!room) return base;

  const totalSnakes = Math.max(0, room.players.size + room.botIds.size);

  // Com arenas grandes, reduzimos um pouco a rede sem mexer na física de 30 Hz.
  // Isso torna 35 jogadores por servidor mais seguro para PC e principalmente mobile.
  if (totalSnakes >= 28) {
    return {
      ...base,
      worldHz:Math.min(base.worldHz,7),
      segmentLimit:Math.min(base.segmentLimit,38),
      foodHz:Math.min(base.foodHz,1),
      interpolationHint:Math.max(base.interpolationHint,0.14)
    };
  }

  if (totalSnakes >= 20) {
    return {
      ...base,
      worldHz:Math.min(base.worldHz,8),
      segmentLimit:Math.min(base.segmentLimit,46),
      foodHz:Math.min(base.foodHz,1),
      interpolationHint:Math.max(base.interpolationHint,0.12)
    };
  }

  if (totalSnakes >= 14) {
    return {
      ...base,
      worldHz:Math.min(base.worldHz,10),
      segmentLimit:Math.min(base.segmentLimit,58),
      interpolationHint:Math.max(base.interpolationHint,0.10)
    };
  }

  return base;

}


function sampleBodyForNetwork(
  snake,
  limit
){

  const body =
    cachedBodySegments(
      snake
    );

  if(
    body.length <=
    limit
  ){

    return body.map(
      point => ({
        x:point.x,
        y:point.y
      })
    );

  }

  const result =
    [];

  const step =
    (
      body.length - 1
    )
    /
    Math.max(
      1,
      limit - 1
    );

  for(
    let i = 0;
    i < limit;
    i++
  ){

    const index =
      Math.min(
        body.length - 1,
        Math.round(
          i * step
        )
      );

    const point =
      body[
        index
      ];

    result.push({
      x:point.x,
      y:point.y
    });

  }

  return result;

}


function applyClientPerformanceProfile(
  player,
  data={}
){

  const tier =
    normalizePerformanceTier(
      data.tier
    );

  player.performanceTier =
    tier;

  player.performanceInfo = {

    tier,

    cores:
      clamp(
        Number(
          data.cores
        )
        ||
        0,
        0,
        128
      ),

    memory:
      clamp(
        Number(
          data.memory
        )
        ||
        0,
        0,
        256
      ),

    mobile:
      data.mobile ===
      true,

    fps:
      clamp(
        Number(
          data.fps
        )
        ||
        0,
        0,
        360
      ),

    quality:
      String(
        data.quality
        ||
        ''
      )
      .slice(
        0,
        20
      )

  };

  const profile =
    networkProfileForPlayer(
      player
    );

  return {

    tier,

    worldHz:
      profile.worldHz,

    segmentLimit:
      profile.segmentLimit,

    foodHz:
      profile.foodHz,

    interpolationHint:
      profile.interpolationHint

  };

}


/* =========================================================
   V13 - MÉTRICAS DE RUNTIME
========================================================= */

const runtimeMetrics = {

  startedAt:
    Date.now(),

  physicsTicks:
    0,

  worldPackets:
    0,

  foodPackets:
    0,

  joins:
    0,

  disconnects:
    0,

  deaths:
    0,

  limitedPurchases:
    0,

  bugReports:
    0

};


function runtimeSnapshot(){

  const memory =
    process.memoryUsage();

  return {

    uptimeSeconds:
      Math.floor(
        process.uptime()
      ),

    node:
      process.version,

    platform:
      `${os.platform()} ${os.arch()}`,

    memory:{
      rss:
        memory.rss,

      heapUsed:
        memory.heapUsed,

      heapTotal:
        memory.heapTotal
    },

    metrics:{
      ...runtimeMetrics
    },

    humans:
      [
        ...players.values()
      ]
      .filter(
        player =>
          !player.isBot
      )
      .length,

    bots:
      [
        ...players.values()
      ]
      .filter(
        player =>
          player.isBot
      )
      .length

  };

}


/* =========================================================
   PUBLIC SERVERS
========================================================= */

const PUBLIC_SERVER_DEFS = [
  { id: 'BR-001', name: 'Brasil #1', region: 'BR', flag: '🇧🇷' },
  { id: 'BR-002', name: 'Brasil #2', region: 'BR', flag: '🇧🇷' },
  { id: 'BR-003', name: 'Brasil #3', region: 'BR', flag: '🇧🇷' },
  { id: 'US-001', name: 'US East #1', region: 'US', flag: '🇺🇸' },
  { id: 'US-002', name: 'US West #1', region: 'US', flag: '🇺🇸' },
  { id: 'EU-001', name: 'Europa #1', region: 'EU', flag: '🇪🇺' },
  { id: 'EU-002', name: 'Europa #2', region: 'EU', flag: '🇪🇺' },
  { id: 'AS-001', name: 'Ásia #1', region: 'AS', flag: '🌏' }
];

const BOT_NAMES = [
  'Nox','Kira','Luna','Rex','Maya','Neo','Viper','Sky','Axel','Iris',
  'Dash','Milo','Nova','Jinx','Echo','Bolt','Pixel','Onyx','Kai','Zara',
  'Drake','Mika','Raven','Zero','Nyx','Toby','Flux','Ace','Orion','Blaze',
  'Storm','Astra','Frost','Jade','Sonic','Rogue','Atlas','Volt','Comet','Ghost'
];

const BOT_SKINS = [
  'basic',
  'fish',
  'shark',
  'venom',
  'dragon',
  'lion',
  'robot',
  'robotPink',
  'retro',
  'rainbow',
  'arcade',
  'disco',
  'tiger',
  'wolf',
  'panda',
  'axolotl',
  'peacock',
  'unicorn',
  'capybara',
  'alien',
  'octopus',
  'crab',
  'lizard'
];

const BOT_COLORS = [
  '#38a8ff','#ff5574','#a879ff','#ffd447','#ff8b38','#22d3ee',
  '#e879f9','#8cff55','#35e69b','#f472b6','#fb7185','#60a5fa'
];

const FOOD_COLORS = [
  '#35e69b','#38a8ff','#ff5574','#a879ff','#ffd447','#ff8b38','#22d3ee','#e879f9'
];

/* =========================================================
   UTILITIES
========================================================= */

function rand(min, max) {
  return Math.random() * (max - min) + min;
}

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function norm(angle) {
  return Math.atan2(Math.sin(angle), Math.cos(angle));
}

function safeAck(ack, payload) {
  if (typeof ack !== 'function') return;
  try { ack(payload); } catch (error) {
    console.error('ACK error:', error?.message || error);
  }
}

function uid(prefix = 'ID') {
  return `${prefix}-${crypto.randomBytes(6).toString('hex')}`;
}

function sanitizeName(value) {
  return String(value ?? 'Player').replace(/[<>]/g, '').trim().slice(0, 18) || 'Player';
}

function sanitizeSkin(value) {
  return String(value ?? 'basic').replace(/[^a-zA-Z0-9_-]/g, '').slice(0, 40) || 'basic';
}

function sanitizeRoomName(value, owner) {
  return String(value ?? '').replace(/[<>]/g, '').trim().slice(0, 28)
    || `Sala de ${owner}`.slice(0, 28);
}

function makeRoomCode() {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let tail = '';
  for (let i = 0; i < 4; i++) tail += chars[crypto.randomInt(0, chars.length)];
  return `WILD-${tail}`;
}

function uniqueRoomCode() {
  let code;
  do { code = makeRoomCode(); } while (privateRooms.has(code));
  return code;
}

/* =========================================================
   ROOM MODEL
========================================================= */

function createRoom({
  code,
  name,
  type = 'private',
  hostId = null,
  botsEnabled = false,
  botCount = 0,
  started = false,
  region = null,
  flag = '🌐'
}) {
  return {
    code,
    name,
    type,
    hostId,
    botsEnabled,
    botCount,
    started,
    region,
    flag,
    players: new Set(),
    botIds: new Set(),
    foods: new Map(),
    createdAt: Date.now(),
    active: type === 'private',
    waitingForPlayers: false,
    soloSince: 0,
    lastHumanCount: 0,
    leaderId: null,
    foodRevision: 0,
    worldSequence: 0,
    soloNoticeSent: false
  };
}

for (const def of PUBLIC_SERVER_DEFS) {
  publicRooms.set(def.id, createRoom({
    code: def.id,
    name: def.name,
    type: 'public',
    started: true,
    botsEnabled: true,
    region: def.region,
    flag: def.flag
  }));
}

function getRoom(code) {
  return publicRooms.get(code) || privateRooms.get(code) || null;
}

function roomHumans(room) {
  return [...room.players].map(id => players.get(id)).filter(Boolean);
}

function roomBots(room) {
  return [...room.botIds].map(id => players.get(id)).filter(Boolean);
}

function roomSnakes(room) {
  return [...room.players, ...room.botIds].map(id => players.get(id)).filter(Boolean);
}

function activeRoomSnakes(room) {
  return roomSnakes(room).filter(s => s.alive);
}

/* =========================================================
   FOOD
========================================================= */

function randomPoint() {
  const angle = rand(0, Math.PI * 2);
  const radius = Math.sqrt(Math.random()) * (SAFE_RADIUS - 120);
  return {
    x: Math.cos(angle) * radius,
    y: Math.sin(angle) * radius
  };
}

function spawnFood(room, x = null, y = null, value = null, color = null) {
  if (room.foods.size >= FOOD_HARD_LIMIT) return null;

  const point = x == null || y == null ? randomPoint() : { x, y };
  const food = {
    id: uid('F'),
    x: point.x,
    y: point.y,
    value: value ?? Math.floor(rand(1, 5)),
    r: rand(4, 7),
    color: color || FOOD_COLORS[Math.floor(rand(0, FOOD_COLORS.length))]
  };

  room.foods.set(
    food.id,
    food
  );

  room.foodRevision =
    (
      room.foodRevision
      ||
      0
    )
    +
    1;

  return food;
}

function ensureFood(room) {
  if (!room || (room.type === 'public' && room.players.size === 0)) return;
  while (room.foods.size < FOOD_TARGET) spawnFood(room);
}

/* =========================================================
   SPAWN
========================================================= */

function findSpawn(room) {
  const alive = activeRoomSnakes(room);

  for (let tries = 0; tries < 120; tries++) {
    const angle = rand(0, Math.PI * 2);
    const radius = rand(500, SAFE_RADIUS - 500);
    const x = Math.cos(angle) * radius;
    const y = Math.sin(angle) * radius;

    if (alive.every(s => Math.hypot(x - s.x, y - s.y) > 500)) {
      return { x, y };
    }
  }

  return { x: rand(-700, 700), y: rand(-700, 700) };
}

/* =========================================================
   TRAIL / BODY
========================================================= */

function seedTrail(snake) {
  snake.trail = [];
  for (let i = 0; i < 700; i++) {
    snake.trail.push({
      x: snake.x - Math.cos(snake.angle) * i * 3,
      y: snake.y - Math.sin(snake.angle) * i * 3
    });
  }
  const seededBody = bodySegments(snake, 0).map(p => ({ x: p.x, y: p.y }));
  snake.bodySegmentsCache = seededBody;
  snake.prevBodySegments = seededBody.map(p => ({ x: p.x, y: p.y }));
  snake.bodyBoundsCache = bodyBounds(seededBody);
}

function updateTrail(snake) {
  snake.trail.unshift({ x: snake.x, y: snake.y });

  const maxTrail = Math.max(
    220,
    Math.ceil(snake.length * SEGMENT_SPACING / 3) + 130
  );

  if (snake.trail.length > maxTrail) snake.trail.length = maxTrail;
}

function bodySegments(snake, offset = 0) {
  if (!Array.isArray(snake.trail) || snake.trail.length === 0) return [];

  const count = Math.max(8, Math.floor(snake.length));
  const result = [];

  for (let i = 0; i < count; i++) {
    const index = Math.min(
      snake.trail.length - 1,
      offset + Math.floor(i * SEGMENT_SPACING / 3)
    );
    const point = snake.trail[index];
    if (point) result.push(point);
  }

  return result;
}


/* =========================================================
   V13.33 - CACHE DE CORPO / BROAD PHASE
   Um corpo é calculado uma vez por tick e reutilizado em:
   colisões + snapshots de rede. Isso corta muito trabalho repetido.
========================================================= */

function bodyBounds(points) {
  if (!Array.isArray(points) || !points.length) {
    return null;
  }

  let minX = points[0].x;
  let maxX = points[0].x;
  let minY = points[0].y;
  let maxY = points[0].y;

  for (let i = 1; i < points.length; i++) {
    const p = points[i];
    if (!p) continue;
    if (p.x < minX) minX = p.x;
    if (p.x > maxX) maxX = p.x;
    if (p.y < minY) minY = p.y;
    if (p.y > maxY) maxY = p.y;
  }

  return { minX, maxX, minY, maxY };
}

function cachedBodySegments(snake) {
  if (
    Array.isArray(snake.bodySegmentsCache)
    &&
    snake.bodySegmentsCache.length
  ) {
    return snake.bodySegmentsCache;
  }

  const body = bodySegments(snake, 0).map(p => ({ x:p.x, y:p.y }));
  snake.bodySegmentsCache = body;
  snake.bodyBoundsCache = bodyBounds(body);
  return body;
}

function refreshBodyCache(snake) {
  const body = bodySegments(snake, 0).map(p => ({ x:p.x, y:p.y }));
  snake.bodySegmentsCache = body;
  snake.bodyBoundsCache = bodyBounds(body);
  return body;
}

function sweptHeadMayTouchBody(attacker, defender, padding = HEAD_BODY_DISTANCE + 8) {
  const bounds =
    defender.bodyBoundsCache
    ||
    bodyBounds(cachedBodySegments(defender));

  if (!bounds) return false;

  const minX = Math.min(attacker.prevX, attacker.x) - padding;
  const maxX = Math.max(attacker.prevX, attacker.x) + padding;
  const minY = Math.min(attacker.prevY, attacker.y) - padding;
  const maxY = Math.max(attacker.prevY, attacker.y) + padding;

  return !(
    maxX < bounds.minX
    ||
    minX > bounds.maxX
    ||
    maxY < bounds.minY
    ||
    minY > bounds.maxY
  );
}

/* =========================================================
   PLAYER MODEL
========================================================= */

function createHuman(socket) {
  return {
    id: socket.id,
    name: 'Player',
    skinId: 'basic',
    color: '#35e69b',
    roomId: null,
    roomType: null,
    ready: false,
    alive: false,
    isBot: false,
    x: 0,
    y: 0,
    prevX: 0,
    prevY: 0,
    angle: 0,
    targetAngle: 0,
    speed: BASE_SPEED,
    boost: false,
    length: 18,
    score: 0,
    foodEaten: 0,
    kills: 0,
    trail: [],
    prevBodySegments: [],
    lastInput: Date.now(),
    startedAt: 0,
    respawnAt: 0,
    waitingSolo: false,
    pendingPublicResume: false,
    connectedAt: Date.now(),
    inArena: false,
    matchId: null,
    performanceTier: 'medium',
    performanceInfo: null,
    lastWorldSentAt: 0,
    lastFoodSentAt: 0,
    socketSequence: 0,
    profileId: socket.data?.gameSession?.accountId || null,
    accountId: socket.data?.gameSession?.accountId || null,
    authenticated: !!socket.data?.gameSession,
    accountDisplayName: socket.data?.gameAccount?.display_name || null,
    accountEquippedSkin: socket.data?.gameAccount?.equipped_skin || 'basic',
    ownedSkins: new Set(socket.data?.ownedSkins || ['basic'])
  };
}

function prepareSnake(snake, room) {
  const spawn = findSpawn(room);

  snake.x = spawn.x;
  snake.y = spawn.y;
  snake.prevX = spawn.x;
  snake.prevY = spawn.y;
  snake.angle = rand(-Math.PI, Math.PI);
  snake.targetAngle = snake.angle;
  snake.boost = false;
  snake.length = 18;
  snake.score = 0;
  snake.foodEaten = 0;
  snake.kills = 0;
  snake.alive = true;
  snake.startedAt = Date.now();
  snake.matchId = uid('MATCH');
  snake.respawnAt = 0;
  snake.lastInput = Date.now();
  snake.waitingSolo = false;
  snake.pendingPublicResume = false;
  snake.inArena = true;
  seedTrail(snake);
}

function currentLeaderId(room) {
  const alive = activeRoomSnakes(room).filter(
    snake => !snake.waitingSolo && snake.inArena !== false
  );
  if (!alive.length) return null;

  alive.sort((a, b) =>
    (b.foodEaten || 0) - (a.foodEaten || 0)
    || (b.score || 0) - (a.score || 0)
    || (b.length || 0) - (a.length || 0)
    || (b.kills || 0) - (a.kills || 0)
    || String(a.id).localeCompare(String(b.id))
  );

  return alive[0].id;
}

function serializePlayer(snake, leaderId = null, segmentLimit = 70) {
  return {
    id: snake.id,
    name: snake.name,
    skinId: snake.skinId,
    color: snake.color,
    x: snake.x,
    y: snake.y,
    prevX: snake.prevX,
    prevY: snake.prevY,
    angle: snake.angle,
    boost: !!snake.boost,
    length: snake.length,
    score: snake.score,
    foodEaten: Math.max(0, Math.floor(Number(snake.foodEaten) || 0)),
    kills: snake.kills || 0,
    alive: !!snake.alive,
    isBot: !!snake.isBot,
    isLeader: snake.id === leaderId,
    segments: sampleBodyForNetwork(
      snake,
      segmentLimit
    )
  };
}

function serializePublicRoom(room) {
  return {
    id: room.code,
    name: room.name,
    region: room.region,
    flag: room.flag,
    humans: room.players.size,
    bots: room.botIds.size,
    total: room.players.size + room.botIds.size,
    displayedPlayers: room.players.size + room.botIds.size,
    botAssisted: room.botIds.size > 0,
    active: room.players.size > 0,
    waitingForPlayers: false,
    max: MAX_ROOM_PLAYERS,
    leaderId: room.leaderId,
    version: GAME_VERSION
  };
}

/* =========================================================
   BOTS
========================================================= */

function uniqueBotName(room, index) {
  const used = new Set(roomSnakes(room).map(s => s.name));

  for (let offset = 0; offset < BOT_NAMES.length; offset++) {
    const name = BOT_NAMES[(index + offset) % BOT_NAMES.length];
    if (!used.has(name)) return name;
  }

  return `Wild${Math.floor(rand(100, 999))}`;
}

function createBot(room, index) {
  const bot = {
    id: uid('BOT'),
    name: uniqueBotName(room, index),
    skinId: BOT_SKINS[index % BOT_SKINS.length],
    color: BOT_COLORS[index % BOT_COLORS.length],
    roomId: room.code,
    roomType: room.type,
    ready: true,
    alive: false,
    isBot: true,
    x: 0,
    y: 0,
    prevX: 0,
    prevY: 0,
    angle: 0,
    targetAngle: 0,
    speed: BASE_SPEED * rand(0.92, 1.02),
    boost: false,
    length: rand(17, 24),
    score: 0,
    foodEaten: 0,
    kills: 0,
    trail: [],
    prevBodySegments: [],
    aiTimer: rand(0.45, 1.15),
    mistake: rand(0.18, 0.36),
    aggression: rand(0.12, 0.34),
    lastInput: Date.now(),
    startedAt: 0,
    respawnAt: 0,
    waitingSolo: false,
    pendingPublicResume: false,
    inArena: true,
    matchId: null
  };

  players.set(bot.id, bot);
  room.botIds.add(bot.id);
  prepareSnake(bot, room);
  bot.length = rand(17, 24);
  return bot;
}

function removeBot(room, id) {
  room.botIds.delete(id);
  players.delete(id);
}

function removeAllBots(room) {
  for (const id of [...room.botIds]) removeBot(room, id);
}

/*
  V13.20 - Bots públicos inteligentes por servidor:
  - 0 humanos: 0 bots (servidor fica em repouso até alguém entrar);
  - 1..9 humanos: completa a arena até 10 participantes;
  - 7 humanos => 3 bots, 8 => 2, 9 => 1;
  - 10+ humanos: 0 bots;
  - bots nunca ocupam as 35 vagas humanas do servidor.
*/
function desiredPublicBots(humans) {
  const count = Math.max(0, Math.floor(Number(humans) || 0));
  if (count <= 0) return 0;
  if (count >= PUBLIC_BOT_TARGET_TOTAL) return 0;
  return Math.max(0, PUBLIC_BOT_TARGET_TOTAL - count);
}

function rebalancePublicBots(room) {
  if (!room || room.type !== 'public') return;

  const humans = room.players.size;

  if (humans === 0) {
    removeAllBots(room);
    room.foods.clear();
    room.active = false;
    room.waitingForPlayers = false;
    room.soloSince = 0;
    room.lastHumanCount = 0;
    room.leaderId = null;
    return;
  }

  room.active = true;
  ensureFood(room);

  const desired = desiredPublicBots(humans);
  const current = room.botIds.size;

  if (current < desired) {
    for (let i = current; i < desired; i++) createBot(room, i);
  } else if (current > desired) {
    const ids = [...room.botIds];
    for (let i = 0; i < current - desired; i++) removeBot(room, ids[i]);
  }
}

function rebalanceAllPublicBots() {
  for (const room of publicRooms.values()) rebalancePublicBots(room);
}

/* =========================================================
   PRIVATE LOBBY
========================================================= */

function serializeLobby(room) {
  const list = roomHumans(room).map(player => ({
    id: player.id,
    name: player.name,
    skinId: player.skinId,
    ready: !!player.ready,
    host: room.hostId === player.id,
    alive: !!player.alive,
    inArena: player.inArena !== false,
    spectating: room.started && player.inArena === false
  }));

  const readyCount = list.filter(p => p.ready).length;
  const minimumReady = room.botsEnabled && room.botCount > 0 ? 1 : 2;

  return {
    code: room.code,
    name: room.name,
    hostId: room.hostId,
    started: room.started,
    botsEnabled: room.botsEnabled,
    botCount: room.botCount,
    players: list,
    onlineCount: list.length,
    readyCount,
    minimumReady,
    canStart: !room.started
      && list.length >= minimumReady
      && readyCount === list.length,
    version: GAME_VERSION
  };
}

function emitLobby(room) {
  const state = serializeLobby(room);
  io.to(room.code).emit('lobbyState', state);
  return state;
}

/* =========================================================
   ROOM DETACH
========================================================= */

function detachPlayerFromRoom(player, { emitLobbyState = true } = {}) {
  if (!player || !player.roomId) return null;

  const room = getRoom(player.roomId);
  const oldRoomId = player.roomId;

  if (room) {
    room.players.delete(player.id);

    if (room.type === 'private') {
      if (room.players.size === 0) {
        removeAllBots(room);
        room.foods.clear();
        privateRooms.delete(room.code);
      } else {
        if (
          room.hostId ===
          player.id
        ) {
          room.hostId =
            [
              ...room.players
            ][0];
        }

        /*
            Se ninguém mais estiver realmente dentro da arena,
            encerra a rodada e devolve a sala ao estado de lobby.
        */
        finishPrivateRoundIfEmpty(
          room
        );

        if (
          emitLobbyState
        ) {
          emitLobby(
            room
          );
        }
      }
    } else {
      rebalancePublicBots(room);
      updatePublicSoloState(room, true);
    }
  }

  const socket = io.sockets.sockets.get(player.id);
  if (socket) socket.leave(oldRoomId);

  player.roomId = null;
  player.roomType = null;
  player.ready = false;
  player.alive = false;
  player.boost = false;
  player.waitingSolo = false;
  player.pendingPublicResume = false;
  player.inArena = false;

  return room;
}

/* =========================================================
   GEOMETRY
========================================================= */

function pointSeg(px, py, ax, ay, bx, by) {
  const abx = bx - ax;
  const aby = by - ay;
  const den = abx * abx + aby * aby;
  if (den < 1e-9) return Math.hypot(px - ax, py - ay);

  const t = clamp(((px - ax) * abx + (py - ay) * aby) / den, 0, 1);
  const cx = ax + abx * t;
  const cy = ay + aby * t;
  return Math.hypot(px - cx, py - cy);
}

function orientation(ax, ay, bx, by, cx, cy) {
  const value = (by - ay) * (cx - bx) - (bx - ax) * (cy - by);
  if (Math.abs(value) < 1e-9) return 0;
  return value > 0 ? 1 : 2;
}

function onSegment(ax, ay, bx, by, cx, cy) {
  return bx <= Math.max(ax, cx) + 1e-9
    && bx + 1e-9 >= Math.min(ax, cx)
    && by <= Math.max(ay, cy) + 1e-9
    && by + 1e-9 >= Math.min(ay, cy);
}

function segmentsIntersect(ax, ay, bx, by, cx, cy, dx, dy) {
  const o1 = orientation(ax, ay, bx, by, cx, cy);
  const o2 = orientation(ax, ay, bx, by, dx, dy);
  const o3 = orientation(cx, cy, dx, dy, ax, ay);
  const o4 = orientation(cx, cy, dx, dy, bx, by);

  if (o1 !== o2 && o3 !== o4) return true;
  if (o1 === 0 && onSegment(ax, ay, cx, cy, bx, by)) return true;
  if (o2 === 0 && onSegment(ax, ay, dx, dy, bx, by)) return true;
  if (o3 === 0 && onSegment(cx, cy, ax, ay, dx, dy)) return true;
  if (o4 === 0 && onSegment(cx, cy, bx, by, dx, dy)) return true;
  return false;
}

function segSeg(ax, ay, bx, by, cx, cy, dx, dy) {
  if (segmentsIntersect(ax, ay, bx, by, cx, cy, dx, dy)) return 0;
  return Math.min(
    pointSeg(ax, ay, cx, cy, dx, dy),
    pointSeg(bx, by, cx, cy, dx, dy),
    pointSeg(cx, cy, ax, ay, bx, by),
    pointSeg(dx, dy, ax, ay, bx, by)
  );
}

function sweptHeads(a, b) {
  const r0x = a.prevX - b.prevX;
  const r0y = a.prevY - b.prevY;
  const drx = (a.x - a.prevX) - (b.x - b.prevX);
  const dry = (a.y - a.prevY) - (b.y - b.prevY);
  const den = drx * drx + dry * dry;
  const t = den > 1e-9 ? clamp(-(r0x * drx + r0y * dry) / den, 0, 1) : 0;
  return Math.hypot(r0x + drx * t, r0y + dry * t);
}

function sweptHeadAgainstBody(attacker, defender) {
  /*
    Broad phase barato: se a trajetória da cabeça nem cruza a caixa
    do corpo, evita centenas de testes de segmento.
  */
  if (!sweptHeadMayTouchBody(attacker, defender)) {
    return Infinity;
  }

  const current = cachedBodySegments(defender);
  const previous = Array.isArray(defender.prevBodySegments) && defender.prevBodySegments.length
    ? defender.prevBodySegments
    : current;

  if (current.length < 4) return Infinity;

  let best = Infinity;

  // começa no 2 para não abrir um buraco grande perto da cabeça.
  for (let i = 2; i < current.length - 1; i++) {
    const c1 = current[i];
    const c2 = current[i + 1];
    if (!c1 || !c2) continue;

    best = Math.min(best, segSeg(
      attacker.prevX, attacker.prevY,
      attacker.x, attacker.y,
      c1.x, c1.y,
      c2.x, c2.y
    ));

    const p1 = previous[i];
    const p2 = previous[i + 1];

    if (p1 && p2) {
      // corpo no tick anterior
      best = Math.min(best, segSeg(
        attacker.prevX, attacker.prevY,
        attacker.x, attacker.y,
        p1.x, p1.y,
        p2.x, p2.y
      ));

      // varredura lateral de cada ponto do corpo entre os ticks
      best = Math.min(best, segSeg(
        attacker.prevX, attacker.prevY,
        attacker.x, attacker.y,
        p1.x, p1.y,
        c1.x, c1.y
      ));

      best = Math.min(best, segSeg(
        attacker.prevX, attacker.prevY,
        attacker.x, attacker.y,
        p2.x, p2.y,
        c2.x, c2.y
      ));
    }

    if (best <= HEAD_BODY_DISTANCE) return best;
  }

  return best;
}

/* =========================================================
   DEATH / DROP FOOD
========================================================= */

function scatterDeathFood(room, snake) {
  const body = cachedBodySegments(snake);

  for (let i = 1; i < body.length; i += 2) {
    if (room.foods.size >= FOOD_HARD_LIMIT) break;

    spawnFood(
      room,
      body[i].x + rand(-10, 10),
      body[i].y + rand(-10, 10),
      Math.max(1, Math.min(8, Math.floor((snake.score || 1) / Math.max(1, body.length / 2) / 3) || 1)),
      snake.color
    );
  }
}

function killSnake(room, snake, reason, killer = null) {
  if (!snake || !snake.alive) return;

  /*
    A recompensa é congelada ANTES de remover o jogador da arena.
    Ela usa somente a quantidade de comidas coletadas nesta vida.
    A posição no ranking não altera WildCoins.
  */
  const rewardPreview = snake.isBot
    ? null
    : buildServerMatchRewardPreview(room, snake);

  snake.alive = false;

  runtimeMetrics.deaths++;

  snake.boost = false;
  scatterDeathFood(room, snake);

  if (killer && killer !== snake && killer.alive) {
    killer.kills = (killer.kills || 0) + 1;
    killer.score = (killer.score || 0) + 25;
  }

  if (snake.isBot) {
    snake.respawnAt = Date.now() + rand(1800, 3200);
    return;
  }

  snake.inArena = false;

  const socket = io.sockets.sockets.get(snake.id);

  if (socket) {
    socket.emit('playerDied', {
      reason,
      score: Math.floor(snake.score || 0),
      foodEaten: Math.max(0, Math.floor(Number(snake.foodEaten) || 0)),
      kills: snake.kills || 0,
      length: Number((snake.length || 18).toFixed(1)),
      timeMs: Math.max(0, Date.now() - (snake.startedAt || Date.now())),
      roomId: room.code,
      privateRoom: room.type === 'private',
      matchId: snake.matchId || null,
      reward: rewardPreview,
      rewardEligible: !!snake.accountId && secureDbReady(),
      rewardPending: !!snake.accountId && secureDbReady(),
      rewardStatus: !snake.accountId
        ? 'account_required'
        : (secureDbReady() ? 'pending' : 'backend_unavailable'),
      version: GAME_VERSION
    });

    /*
      O crédito é feito pelo servidor, nunca pelo navegador.
      Não bloqueamos a física / morte aguardando Supabase.
    */
    if (snake.accountId && secureDbReady() && rewardPreview) {
      const rewardMatchId = snake.matchId;

      void grantSecureMatchReward(snake, rewardPreview)
        .then(result => {
          emitMatchRewardResult(
            io.sockets.sockets.get(snake.id),
            result,
            rewardMatchId
          );
        })
        .catch(error => {
          console.error('match reward:', error);
          emitMatchRewardResult(
            io.sockets.sockets.get(snake.id),
            {
              ok: false,
              code: 'MATCH_REWARD_FAILED',
              error: secureErrorMessage(error)
            },
            rewardMatchId
          );
        });
    }
  }

  if (room.type === 'private') emitLobby(room);
}

/* =========================================================
   MOVEMENT
========================================================= */

function moveSnake(snake, dt, turnSpeed = 3.2) {
  const before =
    Array.isArray(snake.bodySegmentsCache) && snake.bodySegmentsCache.length
      ? snake.bodySegmentsCache
      : bodySegments(snake, 0).map(p => ({ x:p.x, y:p.y }));

  snake.prevBodySegments = before;

  const difference = Math.atan2(
    Math.sin(snake.targetAngle - snake.angle),
    Math.cos(snake.targetAngle - snake.angle)
  );

  snake.angle = norm(snake.angle + clamp(difference, -turnSpeed * dt, turnSpeed * dt));

  let speed = snake.speed;

  if (snake.boost && snake.length > MIN_LENGTH) {
    speed *= BOOST_MULT;
    snake.length = Math.max(MIN_LENGTH, snake.length - 0.32 * dt);
  }

  snake.prevX = snake.x;
  snake.prevY = snake.y;
  snake.x += Math.cos(snake.angle) * speed * dt;
  snake.y += Math.sin(snake.angle) * speed * dt;
  updateTrail(snake);

  /*
    O corpo novo é calculado UMA vez.
    Colisão e transmissão reutilizam este mesmo array.
  */
  refreshBodyCache(snake);
}

/* =========================================================
   BOT AI
========================================================= */

function nearestFood(room, bot, maxDistance = 850) {
  let best = null;
  let bestDistance = maxDistance;

  for (const food of room.foods.values()) {
    const d = Math.hypot(food.x - bot.x, food.y - bot.y);
    if (d < bestDistance) {
      bestDistance = d;
      best = food;
    }
  }

  return best;
}

function nearestHuman(room, bot, maxDistance = 900) {
  let best = null;
  let bestDistance = maxDistance;

  for (const human of roomHumans(room)) {
    if (!human.alive || human.waitingSolo) continue;
    const d = Math.hypot(human.x - bot.x, human.y - bot.y);
    if (d < bestDistance) {
      bestDistance = d;
      best = human;
    }
  }

  return best;
}

function updateBot(room, bot, dt) {
  if (!bot.alive) {
    if (bot.respawnAt && Date.now() >= bot.respawnAt) prepareSnake(bot, room);
    return;
  }

  bot.aiTimer -= dt;

  if (bot.aiTimer <= 0) {
    bot.aiTimer = rand(0.48, 1.15);

    const center = Math.hypot(bot.x, bot.y);
    const food = nearestFood(room, bot);
    const human = nearestHuman(room, bot);

    if (center > SAFE_RADIUS - 520) {
      bot.targetAngle = Math.atan2(-bot.y, -bot.x) + rand(-0.28, 0.28);
    } else if (Math.random() < bot.mistake) {
      bot.targetAngle = norm(bot.angle + rand(-1.5, 1.5));
    } else if (human && Math.random() < bot.aggression) {
      bot.targetAngle = Math.atan2(human.y - bot.y, human.x - bot.x) + rand(-0.26, 0.26);
    } else if (food) {
      bot.targetAngle = Math.atan2(food.y - bot.y, food.x - bot.x) + rand(-0.22, 0.22);
    } else {
      bot.targetAngle = norm(bot.angle + rand(-0.85, 0.85));
    }

    bot.boost = bot.length > 20 && Math.random() < 0.06;
  }

  moveSnake(bot, dt, 2.15);
}

/* =========================================================
   FOOD COLLISION
========================================================= */

function eatFood(room, snake) {
  let eaten = 0;

  for (const [id, food] of room.foods) {
    const dx = snake.x - food.x;
    const dy = snake.y - food.y;
    const reach = HEAD_RADIUS + food.r + 4;

    if ((dx * dx + dy * dy) < (reach * reach)) {
      room.foods.delete(id);

      room.foodRevision =
        (room.foodRevision || 0) + 1;
      snake.score += food.value;
      snake.foodEaten = (snake.foodEaten || 0) + 1;
      snake.length += food.value * 0.11;
      eaten++;
      if (eaten >= 3) break;
    }
  }
}

/* =========================================================
   COLLISIONS
========================================================= */

function handleCollisions(room, dt = 1 / TICK_RATE) {
  let alive = activeRoomSnakes(room).filter(s => !s.waitingSolo && s.inArena !== false);

  // Boundary
  const safeRadiusSq = SAFE_RADIUS * SAFE_RADIUS;

  for (const snake of alive) {
    if ((snake.x * snake.x + snake.y * snake.y) > safeRadiusSq) {
      killSnake(room, snake, 'Você saiu da área segura.');
    }
  }

  alive = activeRoomSnakes(room).filter(s => !s.waitingSolo && s.inArena !== false);

  // Head x head: both die.
  for (let i = 0; i < alive.length; i++) {
    const a = alive[i];
    if (!a.alive) continue;

    for (let j = i + 1; j < alive.length; j++) {
      const b = alive[j];
      if (!b.alive) continue;

      const dx = a.x - b.x;
      const dy = a.y - b.y;
      const maxHead = HEAD_HEAD_DISTANCE + Math.max(a.speed, b.speed) * dt + 8;

      /*
        Broad phase: não calcula colisão varrida para cobras claramente distantes.
      */
      if ((dx * dx + dy * dy) > (maxHead * maxHead)) {
        continue;
      }

      const currentDistanceSq = dx * dx + dy * dy;
      const sweptDistance = sweptHeads(a, b);

      if (currentDistanceSq <= HEAD_HEAD_DISTANCE * HEAD_HEAD_DISTANCE || sweptDistance <= HEAD_HEAD_DISTANCE) {
        killSnake(room, a, `Cabeça com cabeça com ${b.name}.`);
        killSnake(room, b, `Cabeça com cabeça com ${a.name}.`);
      }
    }
  }

  alive = activeRoomSnakes(room).filter(s => !s.waitingSolo && s.inArena !== false);

  // Head x body: attacker dies, defender gets the kill.
  for (const attacker of alive) {
    if (!attacker.alive) continue;

    for (const defender of alive) {
      if (attacker === defender || !attacker.alive || !defender.alive) continue;

      const distance = sweptHeadAgainstBody(attacker, defender);

      if (distance <= HEAD_BODY_DISTANCE) {
        killSnake(
          room,
          attacker,
          `Você bateu no corpo de ${defender.name}.`,
          defender
        );
        break;
      }
    }
  }
}

/* =========================================================
   ROOM UPDATE
========================================================= */

function updateRoom(room, dt) {
  if (!room.started) return;

  for (const snake of roomSnakes(room)) {
    if (snake.isBot) {
      updateBot(room, snake, dt);
    } else if (snake.alive && !snake.waitingSolo && snake.inArena !== false) {
      // Snake.io continua andando mesmo quando o mouse fica parado.
      // Se o cliente some por alguns instantes, desligamos apenas o BOOST.
      if (Date.now() - snake.lastInput > HUMAN_INPUT_TIMEOUT_MS) {
        snake.boost = false;
      }

      moveSnake(snake, dt, 3.2);
    }

    if (snake.alive && !snake.waitingSolo && snake.inArena !== false) {
      eatFood(room, snake);
    }
  }

  handleCollisions(room, dt);
  ensureFood(room);
  room.leaderId = currentLeaderId(room);
}

/* =========================================================
   WORLD / FOOD BROADCAST
========================================================= */

function emitWorld(room) {

  room.leaderId =
    currentLeaderId(
      room
    );

  const leaderId =
    room.leaderId;

  const now =
    Date.now();

  const snakes =
    activeRoomSnakes(
      room
    );

  /*
    Cada perfil de rede usa o mesmo snapshot para todos os jogadores
    daquele perfil. Antes, o servidor reconstruía todos os corpos
    novamente para CADA receptor.
  */
  const playerSnapshotCache =
    new Map();

  const getPlayersSnapshot =
    segmentLimit => {

      const key =
        Number(
          segmentLimit
        )
        ||
        34;

      if(
        playerSnapshotCache.has(
          key
        )
      ){
        return playerSnapshotCache.get(
          key
        );
      }

      const snapshot =
        snakes.map(
          snake =>
            serializePlayer(
              snake,
              leaderId,
              key
            )
        );

      playerSnapshotCache.set(
        key,
        snapshot
      );

      return snapshot;

    };

  for(
    const receiver
    of
    roomHumans(
      room
    )
  ){

    const socket =
      io.sockets.sockets.get(
        receiver.id
      );

    if(
      !socket
      ||
      !socket.connected
    ){

      continue;

    }

    const profile =
      networkProfileForPlayer(
        receiver,
        room
      );

    const interval =
      1000
      /
      profile.worldHz;

    if(
      now -
      (
        receiver.lastWorldSentAt
        ||
        0
      )
      <
      interval - 2
    ){

      continue;

    }

    receiver.lastWorldSentAt =
      now;

    receiver.socketSequence =
      (
        receiver.socketSequence
        ||
        0
      )
      +
      1;

    const serverView =
      room.type ===
      'public'
      ?
      serializePublicRoom(
        room
      )
      :
      {

        id:
          room.code,

        name:
          room.name,

        region:
          'PRIVATE',

        flag:
          '🔒',

        humans:
          room.players.size,

        bots:
          room.botIds.size,

        total:
          room.players.size
          +
          room.botIds.size,

        active:
          room.started,

        max:
          MAX_ROOM_PLAYERS,

        leaderId,

        version:
          GAME_VERSION

      };

    /*
      Snapshot de mundo não deve formar fila.
      Se a conexão estiver ocupada, descartamos o snapshot velho:
      o próximo contém o estado mais novo.
    */
    const worldChannel =
      socket.volatile
      ||
      socket;

    worldChannel.emit(
      'worldState',
      {

        roomId:
          room.code,

        serverTime:
          now,

        version:
          GAME_VERSION,

        build:
          BUILD,

        leaderId,

        sequence:
          receiver.socketSequence,

        networkProfile:{
          tier:
            profile.id,

          worldHz:
            profile.worldHz,

          segmentLimit:
            profile.segmentLimit,

          interpolationHint:
            profile.interpolationHint
        },

        server:
          serverView,

        players:
          getPlayersSnapshot(
            profile.segmentLimit
          )

      }
    );

    runtimeMetrics.worldPackets++;

  }

}

function emitFoods(
  room,
  socket = null,
  force = false
){

  const buildPayload =
    ()=>({

      roomId:
        room.code,

      version:
        GAME_VERSION,

      revision:
        room.foodRevision
        ||
        0,

      foods:
        [
          ...room.foods.values()
        ]

    });


  if(
    socket
  ){

    socket.emit(
      'foodState',
      buildPayload()
    );

    runtimeMetrics.foodPackets++;

    return;

  }


  const now =
    Date.now();


  for(
    const receiver
    of
    roomHumans(
      room
    )
  ){

    const receiverSocket =
      io.sockets.sockets.get(
        receiver.id
      );

    if(
      !receiverSocket
      ||
      !receiverSocket.connected
    ){

      continue;

    }

    const profile =
      networkProfileForPlayer(
        receiver,
        room
      );

    const interval =
      1000
      /
      profile.foodHz;

    if(
      !force
      &&
      now -
      (
        receiver.lastFoodSentAt
        ||
        0
      )
      <
      interval - 4
    ){

      continue;

    }

    const revision =
      room.foodRevision
      ||
      0;

    if(
      !force
      &&
      receiver.lastFoodRevisionSent ===
      revision
    ){
      continue;
    }

    receiver.lastFoodSentAt =
      now;

    receiver.lastFoodRevisionSent =
      revision;

    receiverSocket.emit(
      'foodState',
      buildPayload()
    );

    runtimeMetrics.foodPackets++;

  }

}


/* =========================================================
   PUBLIC SERVER SELECTION
========================================================= */

function chooseAutoPublicServer(excludeId = null) {
  const all = [...publicRooms.values()].filter(room =>
    room.code !== excludeId && room.players.size < MAX_ROOM_PLAYERS
  );

  if (!all.length) return null;

  const occupied = all.filter(room => room.players.size > 0);

  if (occupied.length) {
    // JOGAR AGORA concentra jogadores reais no servidor mais populado.
    // Isso faz os bots desaparecerem naturalmente mais cedo.
    occupied.sort((a, b) =>
      b.players.size - a.players.size
      || a.botIds.size - b.botIds.size
      || a.code.localeCompare(b.code)
    );
    return occupied[0];
  }

  // Se todos estão vazios, começa pelo Brasil #1 quando disponível.
  return all.find(room => room.code === 'BR-001') || all[0];
}

function chooseAlternativePublicServer(currentId) {
  const rooms = [...publicRooms.values()].filter(room =>
    room.code !== currentId
    && room.players.size > 0
    && room.players.size < MAX_ROOM_PLAYERS
  );

  // Alternativa também prioriza gente real, não servidor quase vazio.
  rooms.sort((a, b) =>
    b.players.size - a.players.size
    || a.botIds.size - b.botIds.size
    || a.code.localeCompare(b.code)
  );

  return rooms[0] || null;
}

/* =========================================================
   JOIN PUBLIC
========================================================= */

function joinPublicRoom(socket, player, room) {
  detachPlayerFromRoom(player);

  player.roomId = room.code;
  player.roomType = 'public';
  player.ready = true;
  player.waitingSolo = false;
  player.pendingPublicResume = false;

  room.players.add(player.id);
  room.active = true;
  socket.join(room.code);

  prepareSnake(player, room);
  ensureFood(room);
  rebalancePublicBots(room);
  updatePublicSoloState(room, true);

  const payload = {
    ok: true,
    mode: 'public',
    roomId: room.code,
    server: serializePublicRoom(room),
    version: GAME_VERSION,
    player: serializePlayer(player, currentLeaderId(room)),
    worldRadius: WORLD_RADIUS
  };

  // Comida imediatamente ao entrar, sem esperar o interval.
  emitFoods(room, socket);
  return payload;
}

/* =========================================================
   SOLO PUBLIC STATE
========================================================= */

function updatePublicSoloState(room, force = false) {
  if (!room || room.type !== 'public') return;

  const humans = roomHumans(room);
  const count = humans.length;

  room.waitingForPlayers = false;
  room.soloSince = 0;
  room.soloNoticeSent = false;
  room.lastHumanCount = count;

  if (count === 0) return;

  // V13.20: arena pública nunca pausa só porque há um único humano.
  // Os bots completam a partida, então o jogador continua jogando e
  // recebendo XP/WildCoins normalmente pelo backend autoritativo.
  for (const player of humans) {
    if (player.waitingSolo || player.pendingPublicResume) {
      player.waitingSolo = false;
      player.pendingPublicResume = false;
      if (!player.alive || player.inArena === false) {
        prepareSnake(player, room);
      }
    }
  }
}

/* =========================================================
   PRIVATE LOBBY RETURN
========================================================= */

function finishPrivateRoundIfEmpty(room) {
  if (!room || room.type !== 'private' || !room.started) return false;

  const humans = roomHumans(room);
  const anyoneStillInArena = humans.some(
    p => p.alive && p.inArena !== false
  );

  if (anyoneStillInArena) return false;

  room.started = false;
  removeAllBots(room);
  room.foods.clear();

  for (const human of humans) {
    human.alive = false;
    human.inArena = false;
    human.ready = false;
    human.boost = false;
  }

  emitLobby(room);
  return true;
}

/* =========================================================
   STATUS DOS SERVIDORES - PUSH PELO BACKEND
========================================================= */

function buildServerStatusPayload() {
  return {
    online:true,
    game:'WildSnake',
    version:GAME_VERSION,
    build:BUILD,
    connectedHumans:[...players.values()].filter(player => !player.isBot).length,
    publicServers:[...publicRooms.values()].map(serializePublicRoom),
    privateRooms:privateRooms.size,
    serverTime:Date.now()
  };
}

function broadcastServerStatus() {
  io.emit('serverStatus', buildServerStatusPayload());
}

/* =========================================================
   SOCKET.IO
========================================================= */

io.use(async (socket, next) => {
  try {
    const token = String(socket.handshake.auth?.token || '').trim();
    const session = sessionFromToken(token);

    if (token && !session) {
      return next(new Error('Sessão WildSnake expirada. Entre novamente.'));
    }

    socket.data.gameSession = session || null;
    socket.data.gameAccount = null;
    socket.data.ownedSkins = ['basic'];

    if(session){
      const active =
        getActiveAccountSession(session.accountId);

      if(active && active.token !== token){
        return next(
          new Error(
            'Esta conta já está conectada em outro navegador.'
          )
        );
      }

      if(!active){
        activateAccountSession(
          session.accountId,
          token
        );
      }
    }

    if (session && secureDbReady()) {
      const state = await loadSecureGameState(session.accountId);
      if (!state) return next(new Error('Sessão WildSnake inválida.'));
      socket.data.gameAccount = state.account;
      socket.data.ownedSkins = state.ownedSkins;
    }

    next();
  } catch (error) {
    console.error('socket auth:', error?.message || error);
    next(new Error('Falha ao autenticar socket.'));
  }
});

io.on('connection', socket => {
  const player = createHuman(socket);
  players.set(socket.id, player);

  if(player.accountId && socket.data?.gameSession?.token){
    const active =
      activateAccountSession(
        player.accountId,
        socket.data.gameSession.token
      );

    active?.socketIds.add(socket.id);
    if(active) active.lastSeenAt = Date.now();

    cleanupSessionTransfers();

    for(const request of pendingSessionTransfers.values()){
      if(
        request.accountId === String(player.accountId)
        &&
        request.status === 'pending'
      ){
        socket.emit('sessionTransferRequested', {
          requestId:request.requestId,
          createdAt:request.createdAt,
          expiresAt:request.expiresAt,
          message:'Outro navegador está tentando entrar nesta conta.',
          version:GAME_VERSION
        });
      }
    }
  }

  console.log(`✅ conectado ${socket.id}`);
  socket.emit('serverStatus', buildServerStatusPayload());

  socket.on('approveSessionTransfer', (data = {}, ack) => {
    const session = socket.data?.gameSession;

    if(!session){
      return safeAck(ack,{
        ok:false,
        error:'Sessão inválida.'
      });
    }

    const requestId =
      String(data.requestId || '').trim();

    const request =
      pendingSessionTransfers.get(requestId);

    if(
      !request
      ||
      request.status !== 'pending'
      ||
      request.accountId !== String(session.accountId)
      ||
      Date.now() > request.expiresAt
    ){
      return safeAck(ack,{
        ok:false,
        error:'Solicitação expirada ou inválida.'
      });
    }

    request.status = 'approved';
    request.approvedAt = Date.now();

    safeAck(ack,{
      ok:true,
      requestId,
      version:GAME_VERSION
    });

    revokeAccountSession(
      session.accountId,
      'transfer'
    );
  });

  socket.on('denySessionTransfer', (data = {}, ack) => {
    const session = socket.data?.gameSession;

    if(!session){
      return safeAck(ack,{ok:false,error:'Sessão inválida.'});
    }

    const requestId =
      String(data.requestId || '').trim();

    const request =
      pendingSessionTransfers.get(requestId);

    if(
      !request
      ||
      request.accountId !== String(session.accountId)
      ||
      request.status !== 'pending'
    ){
      return safeAck(ack,{
        ok:false,
        error:'Solicitação inválida.'
      });
    }

    request.status = 'denied';
    request.deniedAt = Date.now();

    safeAck(ack,{
      ok:true,
      requestId,
      version:GAME_VERSION
    });
  });

  socket.on('logoutSession', (_data, ack) => {
    const session = socket.data?.gameSession;

    if(session){
      const active =
        getActiveAccountSession(session.accountId);

      if(active && active.token === session.token){
        revokedSessionTokens.add(session.token);
        sessions.delete(session.token);
        activeAccountSessions.delete(String(session.accountId));
      }
    }

    safeAck(ack,{ok:true,version:GAME_VERSION});
  });

  /* -------------------------
     PUBLIC JOIN
  ------------------------- */

  socket.on('joinPublicGame', async (data = {}, ack) => {
    if (!socketEventAllowed(socket, 'joinPublicGame', 8, 10_000)) {
      return safeAck(ack, { ok:false, error:'Muitas tentativas de entrada. Aguarde alguns segundos.' });
    }

    player.name = player.authenticated
      ? sanitizeName(player.accountDisplayName || data.name)
      : sanitizeName(data.name);
    player.skinId = player.authenticated
      ? await secureSkinForAccount(player.accountId, data.skinId)
      : 'basic';

    let room = null;

    if (data.serverId) {
      room = publicRooms.get(String(data.serverId).toUpperCase()) || null;
    } else {
      room = chooseAutoPublicServer();
    }

    if (!room) {
      return safeAck(ack, { ok: false, error: 'Nenhum servidor público disponível.' });
    }

    if (room.players.size >= MAX_ROOM_PLAYERS) {
      return safeAck(ack, { ok: false, error: 'Servidor cheio.' });
    }

    const payload = joinPublicRoom(socket, player, room);
    safeAck(ack, payload);
  });

  /* -------------------------
     ALTERNATIVE SERVER
  ------------------------- */

  socket.on('findAlternativeServer', (_data, ack) => {
    if (!socketEventAllowed(socket, 'findAlternativeServer', 6, 10_000)) return safeAck(ack,{ok:false,error:'Aguarde antes de procurar novamente.'});
    if (player.roomType !== 'public' || !player.roomId) {
      return safeAck(ack, { ok: false, error: 'Você não está em um servidor público.' });
    }

    const target = chooseAlternativePublicServer(player.roomId);

    if (!target) {
      return safeAck(ack, {
        ok: false,
        error: 'Não encontramos outro servidor com jogadores online agora.'
      });
    }

    safeAck(ack, {
      ok: true,
      target: serializePublicRoom(target),
      version: GAME_VERSION
    });
  });

  /* -------------------------
     SWITCH PUBLIC SERVER
  ------------------------- */

  socket.on('switchPublicServer', (data = {}, ack) => {
    if (!socketEventAllowed(socket, 'switchPublicServer', 6, 10_000)) return safeAck(ack,{ok:false,error:'Muitas trocas de servidor.'});
    if (player.roomType !== 'public' || !player.roomId) {
      return safeAck(ack, { ok: false, error: 'Você não está em um servidor público.' });
    }

    const target = publicRooms.get(String(data.serverId || '').toUpperCase());

    if (!target || target.code === player.roomId) {
      return safeAck(ack, { ok: false, error: 'Servidor de destino inválido.' });
    }

    if (target.players.size >= MAX_ROOM_PLAYERS) {
      return safeAck(ack, { ok: false, error: 'O servidor de destino ficou cheio.' });
    }

    const payload = joinPublicRoom(socket, player, target);
    safeAck(ack, payload);
  });

  /* -------------------------
     SOLO ACTION
  ------------------------- */

  socket.on('publicSoloAction', (data = {}, ack) => {
    if (!socketEventAllowed(socket, 'publicSoloAction', 10, 10_000)) return safeAck(ack,{ok:false,error:'Aguarde um instante.'});
    if (player.roomType !== 'public' || !player.roomId) {
      return safeAck(ack, { ok: false, error: 'Você não está em um servidor público.' });
    }

    const room = publicRooms.get(player.roomId);
    if (!room) return safeAck(ack, { ok: false, error: 'Servidor não encontrado.' });

    const action = String(data.action || '');

    if (action === 'wait') {
      // V13.20: não existe mais espera por segundo humano em servidor público.
      // Mantemos o evento apenas por compatibilidade com clientes antigos.
      rebalancePublicBots(room);
      player.waitingSolo = false;
      player.pendingPublicResume = false;
      player.inArena = true;
      if (!player.alive) prepareSnake(player, room);

      return safeAck(ack, {
        ok: true,
        waiting: false,
        botAssisted: room.botIds.size > 0,
        server: serializePublicRoom(room),
        version: GAME_VERSION
      });
    }

    if (action === 'leave') {
      detachPlayerFromRoom(player);
      return safeAck(ack, { ok: true, left: true, version: GAME_VERSION });
    }

    return safeAck(ack, { ok: false, error: 'Ação inválida.' });
  });

  /* -------------------------
     RESUME PUBLIC MATCH
  ------------------------- */

  socket.on('resumePublicMatch', (_data, ack) => {
    if (!socketEventAllowed(socket, 'resumePublicMatch', 8, 10_000)) return safeAck(ack,{ok:false,error:'Aguarde um instante.'});
    if (player.roomType !== 'public' || !player.roomId) {
      return safeAck(ack, { ok: false, error: 'Você não está em um servidor público.' });
    }

    const room = publicRooms.get(player.roomId);

    if (!room) {
      return safeAck(ack, { ok: false, error: 'Servidor público não encontrado.' });
    }

    rebalancePublicBots(room);

    prepareSnake(player, room);
    player.pendingPublicResume = false;
    player.waitingSolo = false;
    room.waitingForPlayers = false;

    const payload = {
      ok: true,
      mode: 'public',
      roomId: room.code,
      server: serializePublicRoom(room),
      version: GAME_VERSION,
      player: serializePlayer(player, currentLeaderId(room)),
      worldRadius: WORLD_RADIUS
    };

    emitFoods(room, socket);
    safeAck(ack, payload);
  });

  /* -------------------------
     CREATE PRIVATE ROOM
  ------------------------- */

  socket.on('createPrivateRoom', async (data = {}, ack) => {
    if (!socketEventAllowed(socket, 'createPrivateRoom', 4, 10_000)) {
      return safeAck(ack, { ok:false, error:'Muitas salas criadas em pouco tempo.' });
    }

    detachPlayerFromRoom(player);

    player.name = player.authenticated
      ? sanitizeName(player.accountDisplayName || data.name)
      : sanitizeName(data.name);
    player.skinId = player.authenticated
      ? await secureSkinForAccount(player.accountId, data.skinId)
      : 'basic';

    const code = uniqueRoomCode();
    const botsEnabled = data.botsEnabled === true;
    const botCount = botsEnabled ? clamp(Number(data.botCount) || 4, 1, 10) : 0;

    const room = createRoom({
      code,
      name: sanitizeRoomName(data.roomName, player.name),
      type: 'private',
      hostId: player.id,
      botsEnabled,
      botCount,
      started: false,
      flag: '🔒'
    });

    privateRooms.set(code, room);
    room.players.add(player.id);

    player.roomId = code;
    player.roomType = 'private';
    player.ready = false;
    player.alive = false;

    socket.join(code);

    const lobby = serializeLobby(room);
    const payload = { ok: true, code, lobby, version: GAME_VERSION };

    safeAck(ack, payload);
    socket.emit('roomCreated', payload);
    emitLobby(room);
  });

  /* -------------------------
     JOIN PRIVATE ROOM
  ------------------------- */

  socket.on('joinPrivateRoom', async (data = {}, ack) => {
    if (!socketEventAllowed(socket, 'joinPrivateRoom', 8, 30_000)) {
      return safeAck(ack, { ok:false, error:'Muitas tentativas de código. Aguarde um pouco.' });
    }

    const code = String(data.code || '').trim().toUpperCase();
    const room = privateRooms.get(code);

    if (!room) {
      return safeAck(ack, { ok: false, error: 'Sala não encontrada. Confira o código WILD-XXXX.' });
    }

    if (room.players.size >= MAX_ROOM_PLAYERS) {
      return safeAck(ack, { ok: false, error: 'Sala cheia.' });
    }

    detachPlayerFromRoom(player);

    player.name = player.authenticated
      ? sanitizeName(player.accountDisplayName || data.name)
      : sanitizeName(data.name);
    player.skinId = player.authenticated
      ? await secureSkinForAccount(player.accountId, data.skinId)
      : 'basic';
    player.roomId = code;
    player.roomType = 'private';
    player.ready = room.started;
    player.alive = false;

    room.players.add(player.id);
    socket.join(code);

    let arena = null;

    if (room.started) {
      prepareSnake(player, room);
      ensureFood(room);

      arena = {
        ok: true,
        mode: 'private',
        roomId: code,
        player: serializePlayer(player, currentLeaderId(room)),
        worldRadius: WORLD_RADIUS,
        version: GAME_VERSION
      };
    }

    const lobby = serializeLobby(room);
    const payload = { ok: true, code, started: room.started, lobby, arena, version: GAME_VERSION };

    safeAck(ack, payload);
    socket.emit('roomJoined', payload);

    if (arena) {
      socket.emit('onlineJoined', arena);
      emitFoods(room, socket);
    }

    emitLobby(room);
  });

  /* -------------------------
     READY
  ------------------------- */

  socket.on('toggleReady', (_data, ack) => {
    if (!socketEventAllowed(socket, 'toggleReady', 12, 10_000)) return safeAck(ack,{ok:false,error:'Muitas alterações de pronto.'});
    const room = player.roomType === 'private' ? privateRooms.get(player.roomId) : null;

    if (!room) {
      return safeAck(ack, { ok: false, error: 'Você não está em uma sala.' });
    }

    if (room.started) {
      return safeAck(ack, { ok: false, error: 'A partida já começou.' });
    }

    player.ready = !player.ready;
    const lobby = emitLobby(room);

    safeAck(ack, {
      ok: true,
      ready: player.ready,
      lobby
    });
  });

  /* -------------------------
     START PRIVATE GAME
  ------------------------- */

  socket.on('startPrivateGame', (_data, ack) => {
    if (!socketEventAllowed(socket, 'startPrivateGame', 6, 10_000)) return safeAck(ack,{ok:false,error:'Aguarde antes de iniciar novamente.'});
    const room = player.roomType === 'private' ? privateRooms.get(player.roomId) : null;

    if (!room) {
      return safeAck(ack, { ok: false, error: 'Você não está em uma sala.' });
    }

    if (room.hostId !== player.id) {
      return safeAck(ack, { ok: false, error: 'Somente o dono da sala pode iniciar.' });
    }

    const lobby = serializeLobby(room);

    if (!lobby.canStart) {
      return safeAck(ack, {
        ok: false,
        error: room.botsEnabled
          ? 'Todos os jogadores devem marcar PRONTO.'
          : 'São necessários pelo menos 2 jogadores e todos devem marcar PRONTO.'
      });
    }

    room.started = true;
    room.foods.clear();
    ensureFood(room);
    removeAllBots(room);

    for (const id of room.players) {
      const roomPlayer = players.get(id);
      if (!roomPlayer) continue;

      roomPlayer.ready = true;
      prepareSnake(roomPlayer, room);

      const roomSocket = io.sockets.sockets.get(id);
      if (roomSocket) {
        roomSocket.emit('onlineJoined', {
          ok: true,
          mode: 'private',
          roomId: room.code,
          player: serializePlayer(roomPlayer, currentLeaderId(room)),
          worldRadius: WORLD_RADIUS,
          version: GAME_VERSION
        });
        emitFoods(room, roomSocket);
      }
    }

    if (room.botsEnabled) {
      for (let i = 0; i < room.botCount; i++) createBot(room, i);
    }

    io.to(room.code).emit('roomGameStarted', {
      ok: true,
      roomId: room.code,
      botsEnabled: room.botsEnabled,
      botCount: room.botCount,
      version: GAME_VERSION
    });

    emitLobby(room);
    emitFoods(room);

    safeAck(ack, { ok: true, roomId: room.code, version: GAME_VERSION });
  });

  /* -------------------------
     RESPAWN
  ------------------------- */

  socket.on('respawn', (_data, ack) => {
    if (!socketEventAllowed(socket, 'respawn', 8, 10_000)) return safeAck(ack,{ok:false,error:'Muitas tentativas de renascer.'});
    const room = player.roomId ? getRoom(player.roomId) : null;

    if (!room || !room.started) {
      return safeAck(ack, { ok: false, error: 'Não há partida ativa.' });
    }

    if (room.type === 'public') {
      rebalancePublicBots(room);
    }

    prepareSnake(player, room);
    player.ready = true;

    const payload = {
      ok: true,
      mode: player.roomType,
      roomId: room.code,
      player: serializePlayer(player, currentLeaderId(room)),
      worldRadius: WORLD_RADIUS,
      version: GAME_VERSION
    };

    emitFoods(room, socket);
    safeAck(ack, payload);

    if (room.type === 'private') emitLobby(room);
  });

  /* -------------------------
     INPUT
  ------------------------- */

  socket.on('input', (data = {}) => {
    if (!socketEventAllowed(socket, 'input', 100, 1_000)) return;
    if (!player.roomId || !player.alive || player.waitingSolo) return;

    const room = getRoom(player.roomId);
    if (!room || !room.started) return;

    if (Number.isFinite(data.angle)) player.targetAngle = norm(data.angle);
    player.boost = data.boost === true;
    player.lastInput = Date.now();
  });

  /* -------------------------
     PING
  ------------------------- */

  socket.on('clientPing', sentAt => {
    if (!socketEventAllowed(socket, 'clientPing', 20, 10_000)) return;
    socket.emit('serverPong', sentAt);
  });

  /* -------------------------
     REFRESH AUTH / SKINS
  ------------------------- */

  socket.on('refreshIdentity', async (_data, ack) => {
    if (!socketEventAllowed(socket, 'refreshIdentity', 8, 10_000)) {
      return safeAck(ack, { ok:false, error:'Aguarde alguns segundos.' });
    }

    if (!player.accountId || !secureDbReady()) {
      player.skinId = 'basic';
      return safeAck(ack, { ok:true, guest:true, skinId:'basic' });
    }

    try {
      const state = await loadSecureGameState(player.accountId);
      if (!state) return safeAck(ack, { ok:false, error:'Conta não encontrada.' });
      player.accountDisplayName = state.account.display_name;
      player.accountEquippedSkin = state.account.equipped_skin || 'basic';
      player.ownedSkins = new Set(state.ownedSkins || ['basic']);
      player.name = sanitizeName(player.accountDisplayName || player.name);
      player.skinId = state.ownedSkins.includes(player.skinId)
        ? player.skinId
        : (state.ownedSkins.includes(state.account.equipped_skin) ? state.account.equipped_skin : 'basic');
      return safeAck(ack, { ok:true, skinId:player.skinId });
    } catch (error) {
      console.error('refreshIdentity:', error?.message || error);
      return safeAck(ack, { ok:false, error:'Falha ao atualizar identidade.' });
    }
  });

  /* -------------------------
     LEAVE ROOM
  ------------------------- */

  socket.on('returnPrivateLobby', (_data, ack) => {
    if (!socketEventAllowed(socket, 'returnPrivateLobby', 8, 10_000)) return safeAck(ack,{ok:false,error:'Aguarde um instante.'});
    if (player.roomType !== 'private' || !player.roomId) {
      return safeAck(ack, {
        ok: false,
        error: 'Você não está em uma sala privada.'
      });
    }

    const room = privateRooms.get(player.roomId);

    if (!room) {
      return safeAck(ack, {
        ok: false,
        error: 'Sala privada não encontrada.'
      });
    }

    player.inArena = false;
    player.alive = false;
    player.boost = false;
    player.ready = false;

    finishPrivateRoundIfEmpty(room);

    const lobby = serializeLobby(room);
    emitLobby(room);

    safeAck(ack, {
      ok: true,
      lobby,
      roomId: room.code,
      version: GAME_VERSION
    });
  });

  socket.on('leaveRoom', (_data, ack) => {
    if (!socketEventAllowed(socket, 'leaveRoom', 12, 10_000)) return safeAck(ack,{ok:false,error:'Aguarde um instante.'});
    detachPlayerFromRoom(player);
    safeAck(ack, { ok: true, version: GAME_VERSION });
  });

  /* -------------------------
     DISCONNECT
  ------------------------- */

  socket.on('disconnect', reason => {
    detachPlayerFromRoom(player);
    players.delete(player.id);

    const session =
      socket.data?.gameSession;

    if(session?.accountId){
      const active =
        getActiveAccountSession(
          session.accountId
        );

      if(active && active.token === session.token){
        active.socketIds.delete(socket.id);
        active.lastSeenAt = Date.now();

        if(active.socketIds.size === 0){
          scheduleAccountSessionRelease(
            session.accountId,
            session.token
          );
        }
      }
    }

    console.log(`❌ saiu ${socket.id}: ${reason}`);
  });
});

/* =========================================================
   SERVER LOOPS
========================================================= */

const DT = 1 / TICK_RATE;
let lastPhysicsTickAt = Date.now();

setInterval(() => {
  const now = Date.now();
  const elapsed = Math.max(
    1 / 120,
    Math.min(
      0.05,
      (now - lastPhysicsTickAt) / 1000
    )
  );

  lastPhysicsTickAt = now;

  for (const room of publicRooms.values()) {
    if (room.players.size > 0) updateRoom(room, elapsed);
  }

  for (const room of privateRooms.values()) {
    if (room.started) updateRoom(room, elapsed);
  }
}, 1000 / TICK_RATE);

setInterval(() => {
  rebalanceAllPublicBots();

  for (const room of publicRooms.values()) {
    updatePublicSoloState(room, false);
  }
}, 500);

setInterval(() => {
  for (const room of publicRooms.values()) {
    if (room.players.size > 0) emitWorld(room);
  }

  for (const room of privateRooms.values()) {
    if (room.started) emitWorld(room);
  }
}, 1000 / WORLD_BROADCAST_RATE);

setInterval(() => {
  for (const room of publicRooms.values()) {
    if (room.players.size > 0) emitFoods(room);
  }

  for (const room of privateRooms.values()) {
    if (room.started) emitFoods(room);
  }
}, 1000 / FOOD_BROADCAST_RATE);

/*
   Atualização das arenas feita no BACKEND.
   O navegador apenas atualiza os números já desenhados.
*/
setInterval(broadcastServerStatus, 3000);

/* =========================================================
   V13.10 - API SEGURA DE CONFIG / AUTH / CONTA / ECONOMIA
========================================================= */

app.get('/api/public-config', (_req, res) => {
  res.set('Cache-Control', 'no-store');
  res.json({
    ok:true,
    supabaseUrl:SUPABASE_URL,
    supabasePublishableKey:SUPABASE_PUBLISHABLE_KEY || null,
    secureBackendReady:secureDbReady(),
    googleOAuthReady:googleOAuthReady(),
    googleOAuthStart:'/api/auth/google/start',
    configuration:supabaseConfigDiagnostics(),
    version:GAME_VERSION
  });
});


app.post('/api/account/qr-auto', async (req, res) => {
  const key = `qr-auto:${req.ip}`;

  if (!rateLimit(key, { windowMs:60_000, max:5 })) {
    return res.status(429).json({
      ok:false,
      error:'Muitas contas automáticas foram solicitadas. Aguarde um minuto.'
    });
  }

  /*
     Se o navegador já possui uma sessão válida, reutiliza a conta.
     Isso impede criar contas novas desnecessariamente ao ler vários QR Codes.
  */
  const existingSession = sessionFromRequest(req);

  if (existingSession) {
    try {
      const state = await loadSecureGameState(existingSession.accountId);

      if (state) {
        return res.json({
          ok:true,
          reused:true,
          autoCreated:false,
          token:existingSession.token,
          account:secureAccountView(state)
        });
      }
    } catch (error) {
      console.error('qr auto existing session:', error?.message || error);
    }
  }

  try {
    const result = await createQrGuestAccount();

    return res
      .status(result.status || (result.ok ? 200 : 400))
      .json(result);
  } catch (error) {
    console.error('qr auto account:', error);

    return res
      .status(error.status === 503 ? 503 : 500)
      .json({
        ok:false,
        error:secureErrorMessage(error)
      });
  }
});


app.get('/api/private-room/invite/:code', (req, res) => {
  const code = String(req.params.code || '').trim().toUpperCase();

  if (!/^WILD-[A-Z0-9]{4}$/.test(code)) {
    return res.status(400).json({
      ok:false,
      exists:false,
      error:'Código de sala inválido.'
    });
  }

  const room = privateRooms.get(code);

  if (!room) {
    return res.status(404).json({
      ok:false,
      exists:false,
      code,
      error:'Esta sala não existe mais.'
    });
  }

  return res.json({
    ok:true,
    exists:true,
    code,
    name:room.name || 'Sala WildSnake',
    started:!!room.started,
    players:room.players?.size || 0,
    maxPlayers:room.maxPlayers || 50,
    version:GAME_VERSION
  });
});


app.post('/api/account/register', async (req, res) => {
  const key = `register:${req.ip}`;
  if (!rateLimit(key, { windowMs:60_000, max:6 })) {
    return res.status(429).json({ ok:false, error:'Muitas tentativas. Aguarde um minuto.' });
  }

  try {
    const result = await createSecureLocalAccount(req.body || {});
    return res.status(result.status || (result.ok ? 200 : 400)).json(result);
  } catch (error) {
    console.error('secure register:', error);
    return res.status(error.status === 503 ? 503 : 500).json({
      ok:false,
      error:secureErrorMessage(error)
    });
  }
});

app.post('/api/account/login', async (req, res) => {
  const key = `login:${req.ip}`;
  if (!rateLimit(key, { windowMs:60_000, max:12 })) {
    return res.status(429).json({ ok:false, error:'Muitas tentativas. Aguarde um minuto.' });
  }

  try {
    const result = await loginSecureLocalAccount(req.body || {});
    return res.status(result.status || (result.ok ? 200 : 401)).json(result);
  } catch (error) {
    console.error('secure login:', error);
    return res.status(error.status === 503 ? 503 : 500).json({
      ok:false,
      error:secureErrorMessage(error)
    });
  }
});


app.get('/api/account/transfer/status', (req, res) => {
  cleanupSessionTransfers();

  const requestId =
    String(req.query.requestId || '').trim();

  const request =
    pendingSessionTransfers.get(requestId);

  if(!request){
    return res.status(404).json({
      ok:false,
      status:'expired',
      error:'Solicitação não encontrada ou expirada.'
    });
  }

  return res.json({
    ok:true,
    requestId,
    status:request.status,
    expiresAt:request.expiresAt,
    version:GAME_VERSION
  });
});

/* =========================================================
   GOOGLE OAUTH - INÍCIO DIRETO PELO BACKEND
========================================================= */

app.get('/api/auth/google/start', (req, res) => {
  if (!googleOAuthReady()) {
    return res.status(503).json({
      ok:false,
      code:'SUPABASE_BACKEND_NOT_READY',
      error:'O backend seguro do Supabase ainda não está configurado no Render.',
      configuration:supabaseConfigDiagnostics()
    });
  }

  const returnPath = String(req.query.return || '/') === '/tutorial.html'
    ? '/tutorial.html'
    : '/';

  const forwardedProto = String(req.headers['x-forwarded-proto'] || '')
    .split(',')[0]
    .trim();

  const protocol = forwardedProto || req.protocol || 'https';
  const host = String(req.get('host') || '');

  if (!host) {
    return res.status(400).json({ok:false,error:'Host inválido.'});
  }

  const redirectTo = `${protocol}://${host}${returnPath}`;
  const authorizeUrl = new URL(`${SUPABASE_URL}/auth/v1/authorize`);

  authorizeUrl.searchParams.set('provider','google');
  authorizeUrl.searchParams.set('redirect_to',redirectTo);
  authorizeUrl.searchParams.set('scopes','openid email profile');

  res.set('Cache-Control','no-store');
  return res.redirect(302, authorizeUrl.toString());
});


app.post('/api/auth/google/resolve', async (req, res) => {
  const key = `google-resolve:${req.ip}`;
  if (!rateLimit(key, { windowMs:60_000, max:15 })) {
    return res.status(429).json({ ok:false, error:'Muitas tentativas. Aguarde um minuto.' });
  }

  try {
    const user = await verifySupabaseUser(readBearerToken(req));
    if (!user) {
      return res.status(401).json({ ok:false, code:'GOOGLE_SESSION_INVALID', error:'Sessão Google/Supabase inválida.' });
    }

    const intent = req.body?.intent === 'create' ? 'create' : 'login';
    const result = await resolveGoogleGameAccount(user, intent);
    return res.status(result.status || (result.ok ? 200 : 400)).json(result);
  } catch (error) {
    console.error('google resolve:', error);
    return res.status(error.status === 503 ? 503 : 500).json({
      ok:false,
      error:secureErrorMessage(error)
    });
  }
});

app.post('/api/account/link-google', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Entre na conta antes de vincular o Google.' });

  const key = `link-google:${session.accountId}`;
  if (!rateLimit(key, { windowMs:60_000, max:6 })) {
    return res.status(429).json({ ok:false, error:'Muitas tentativas de vínculo. Aguarde um minuto.' });
  }

  try {
    const googleToken = String(req.headers['x-supabase-token'] || '').trim();
    const user = await verifySupabaseUser(googleToken);
    if (!user) return res.status(401).json({ ok:false, error:'Google não pôde ser validado.' });

    const result = await linkGoogleToSecureAccount(session.accountId, user);
    return res.status(result.status || (result.ok ? 200 : 400)).json(result);
  } catch (error) {
    console.error('link-google:', error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.get('/api/account/me', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão inválida ou expirada.' });

  try {
    const state = await loadSecureGameState(session.accountId);
    if (!state) return res.status(404).json({ ok:false, error:'Conta não encontrada.' });
    return res.json({ ok:true, account:secureAccountView(state) });
  } catch (error) {
    console.error('account me:', error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.get('/api/account/state', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão inválida ou expirada.' });

  try {
    const state = await loadSecureGameState(session.accountId);
    if (!state) return res.status(404).json({ ok:false, error:'Conta não encontrada.' });
    return res.json({ ok:true, account:secureAccountView(state) });
  } catch (error) {
    console.error('account state:', error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/account/profile', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão inválida.' });

  try {
    const displayName = cleanDisplayName(req.body?.displayName);
    if (displayName.length < 2) {
      return res.status(400).json({ ok:false, error:'Digite um nome válido.' });
    }

    await dbUpdate(
      SECURE_DB_TABLES.accounts,
      { id:`eq.${session.accountId}` },
      { display_name:displayName }
    );

    const state = await loadSecureGameState(session.accountId);
    return res.json({ ok:true, account:secureAccountView(state) });
  } catch (error) {
    console.error('profile update:', error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});


app.get('/api/shop/catalog', async (_req, res) => {
  res.set('Cache-Control', 'no-store');

  try {
    const regular = Object.values(SHOP_SKIN_CATALOG).map(skin => ({
      id:skin.id,
      name:skin.name,
      currency:skin.currency,
      price:skin.price,
      rarity:skin.rarity,
      limited:false,
      comboOnly:COMBO_ONLY_SKIN_IDS.has(skin.id)
    }));

    const limited = Object.values(LIMITED_SKIN_CATALOG).map(skin => ({
      id:skin.id,
      name:skin.name,
      currency:skin.currency,
      price:skin.price,
      rarity:'limited',
      limited:true,
      comboOnly:false
    }));

    return res.json({
      ok:true,
      version:GAME_VERSION,
      economy:{
        gemCoinValue:WILD_GEM_COIN_VALUE,
        cashCurrency:'BRL'
      },
      skins:[...regular,...limited],
      combos:Object.values(SHOP_COMBOS).map(combo => ({
        id:combo.id,
        name:combo.name,
        subtitle:combo.subtitle,
        badge:combo.badge,
        accent:combo.accent,
        coinPrice:combo.coinPrice,
        gemPrice:combo.gemPrice,
        skins:[...combo.skins]
      })),
      packs:SHOP_MONEY_PACKS
    });
  } catch (error) {
    console.error('shop catalog:', error?.message || error);
    return res.status(500).json({ ok:false, error:'Não foi possível carregar o catálogo.' });
  }
});

app.get('/api/shop/limited', async (_req, res) => {
  res.set('Cache-Control', 'no-store');
  try {
    return res.json({
      ok:true,
      version:GAME_VERSION,
      skins:await listLimitedInventorySecure()
    });
  } catch (error) {
    console.error('limited inventory:', error);
    return res.status(500).json({ ok:false, error:'Não foi possível carregar o estoque.' });
  }
});

app.post('/api/shop/purchase', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Entre na sua conta para comprar skins.' });

  const key = `purchase:${session.accountId}`;
  if (!rateLimit(key, { windowMs:10_000, max:6 })) {
    return res.status(429).json({ ok:false, error:'Aguarde alguns segundos antes de comprar novamente.' });
  }

  const skinId = sanitizeSkin(req.body?.skinId);

  if (COMBO_ONLY_SKIN_IDS.has(skinId)) {
    return res.status(409).json({
      ok:false,
      error:'Esta skin é exclusiva do Combo Animais Selvagens.'
    });
  }

  try {
    /*
       Skins limitadas continuam usando a função SQL com estoque atômico.
       Skins avulsas normais usam o catálogo autoritativo V13.17 do servidor,
       então uma tabela antiga no Supabase não consegue cobrar preço errado.
    */
    if (LIMITED_SKIN_CATALOG[skinId]) {
      const result = await dbRpc('ws_purchase_skin', {
        p_account_id:session.accountId,
        p_skin_id:skinId
      });
      runtimeMetrics.limitedPurchases += 1;
      const state = await loadSecureGameState(session.accountId);
      return res.json({ ok:true, purchase:result, account:secureAccountView(state) });
    }

    const result = await purchaseShopSkinForAccount(session.accountId, skinId);
    return res.json({
      ok:true,
      purchase:result.skin,
      account:result.account,
      economy:{ gemCoinValue:WILD_GEM_COIN_VALUE }
    });
  } catch (error) {
    console.error('purchase:', error?.message || error);
    return res.status(409).json({ ok:false, error:secureErrorMessage(error) });
  }
});

// Compatibilidade com versões anteriores do cliente.
app.post('/api/shop/limited/purchase', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });
  try {
    const skinId = sanitizeSkin(req.body?.skinId);
    const result = await dbRpc('ws_purchase_skin', {
      p_account_id:session.accountId,
      p_skin_id:skinId
    });
    const state = await loadSecureGameState(session.accountId);
    const stock = await listLimitedInventorySecure();
    const item = stock.find(x => x.id === skinId);
    return res.json({
      ok:true,
      purchase:result,
      remaining:item?.stock ?? null,
      account:secureAccountView(state)
    });
  } catch (error) {
    return res.status(409).json({ ok:false, error:secureErrorMessage(error) });
  }
});



/* =========================================================
   V13.26 - COMBOS AUTORITATIVOS
========================================================= */

app.post('/api/shop/combo/purchase', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) {
    return res.status(401).json({ ok:false, error:'A conta principal do WildSnake é necessária para gravar a compra.' });
  }

  const key = `combo-purchase:${session.accountId}`;
  if (!rateLimit(key, { windowMs:10_000, max:3 })) {
    return res.status(429).json({ ok:false, error:'Aguarde alguns segundos antes de comprar novamente.' });
  }

  const comboId = String(req.body?.comboId || '').trim();
  const currency = String(req.body?.currency || '').trim().toLowerCase();

  try {
    const result = await purchaseShopComboForAccount(
      session.accountId,
      comboId,
      currency
    );

    return res.json({
      ok:true,
      combo:result.combo,
      account:result.account,
      economy:{ gemCoinValue:WILD_GEM_COIN_VALUE }
    });
  } catch (error) {
    console.error('combo purchase:', error?.message || error);
    return res.status(409).json({ ok:false, error:secureErrorMessage(error) });
  }
});


/* =========================================================
   V13.16 - CAMINHO DE RECOMPENSAS / MUNDOS
========================================================= */

app.get('/api/rewards/progression', async (req, res) => {
  res.set('Cache-Control','no-store');

  const session = sessionFromRequest(req);

  try {
    const progression = await secureProgressionState(session?.accountId || null);

    if (!progression) {
      return res.status(404).json({ ok:false, error:'Conta não encontrada.' });
    }

    return res.json({
      ok:true,
      version:GAME_VERSION,
      progression
    });
  } catch (error) {
    console.error('reward progression:', error?.message || error);
    return res.status(500).json({
      ok:false,
      error:'Não foi possível carregar o caminho de recompensas.'
    });
  }
});

app.post('/api/rewards/claim', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) {
    return res.status(401).json({ ok:false, error:'Entre na sua conta para resgatar recompensas.' });
  }

  const key = `reward-claim:${session.accountId}`;
  if (!rateLimit(key, { windowMs:10_000, max:12 })) {
    return res.status(429).json({ ok:false, error:'Muitos resgates seguidos. Aguarde alguns segundos.' });
  }

  const nodeId = String(req.body?.nodeId || '').trim();
  const node = progressionNodeById(nodeId);

  if (!node) {
    return res.status(404).json({ ok:false, error:'Recompensa inválida.' });
  }

  if (node.reward?.kind === 'skin_roll') {
    return res.status(409).json({
      ok:false,
      code:'USE_SKIN_ROLL',
      error:'Use a roleta para resgatar esta recompensa.'
    });
  }

  try {
    const stateBefore = await loadSecureGameState(session.accountId);
    if (!stateBefore?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const totalXp = totalXpForWallet(stateBefore.wallet);
    if (totalXp < node.xpRequired) {
      return res.status(403).json({
        ok:false,
        code:'XP_INSUFICIENTE',
        error:`Você precisa de ${node.xpRequired.toLocaleString('pt-BR')} XP total para resgatar.`
      });
    }

    const claimResult = await secureClaimProgressionCurrency(session.accountId, node);
    const reward = node.reward || {};
    const progression = await secureProgressionState(session.accountId);

    return res.json({
      ok:true,
      reused:!!claimResult?.reused,
      claim:claimResult?.claim || null,
      reward,
      node,
      progression,
      account:progression?.account || null
    });
  } catch (error) {
    console.error('reward claim:', error?.message || error);
    return res.status(409).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/rewards/roll-skin', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) {
    return res.status(401).json({ ok:false, error:'Entre na sua conta para rodar a roleta.' });
  }

  const key = `reward-roll:${session.accountId}`;
  if (!rateLimit(key, { windowMs:10_000, max:6 })) {
    return res.status(429).json({ ok:false, error:'Aguarde alguns segundos antes de rodar novamente.' });
  }

  const nodeId = String(req.body?.nodeId || '').trim();
  const node = progressionNodeById(nodeId);

  if (!node || node.reward?.kind !== 'skin_roll') {
    return res.status(404).json({ ok:false, error:'Roleta de skin inválida.' });
  }

  try {
    const stateBefore = await loadSecureGameState(session.accountId);
    if (!stateBefore?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const totalXp = totalXpForWallet(stateBefore.wallet);
    if (totalXp < node.xpRequired) {
      return res.status(403).json({
        ok:false,
        code:'XP_INSUFICIENTE',
        error:'Você ainda não desbloqueou esta roleta.'
      });
    }

    const previous = await dbSelect(SECURE_DB_TABLES.ledger, {
      select:'skin_id,metadata',
      account_id:`eq.${session.accountId}`,
      idempotency_key:`eq.progression:${session.accountId}:${node.id}`,
      limit:1
    });

    if (previous.length) {
      const skinId = String(previous[0]?.skin_id || previous[0]?.metadata?.skinId || '');
      const catalog = skinId
        ? await dbSelect(SECURE_DB_TABLES.catalog, {
            select:'skin_id,name,rarity',
            skin_id:`eq.${skinId}`,
            limit:1
          })
        : [];

      const progression = await secureProgressionState(session.accountId);

      return res.json({
        ok:true,
        reused:true,
        result:catalog[0] || {
          skin_id:skinId,
          name:previous[0]?.metadata?.skinName || skinId,
          rarity:previous[0]?.metadata?.rarity || 'rare'
        },
        progression,
        account:progression?.account || null
      });
    }

    let pool = await progressionSkinPool(session.accountId);
    if (!pool.length) {
      return res.status(409).json({
        ok:false,
        code:'NO_SKINS_AVAILABLE',
        error:'Você já possui todas as skins disponíveis nesta roleta.'
      });
    }

    let chosen = null;
    let result = null;
    let lastError = null;

    for (let attempt = 0; attempt < 4; attempt++) {
      chosen = chooseProgressionSkin(pool);
      if (!chosen) break;
      try {
        result = await secureClaimProgressionSkin(session.accountId, node, chosen);
        break;
      } catch (error) {
        lastError = error;
        pool = pool.filter(item => item.skin_id !== chosen.skin_id);
      }
    }

    if (!result || !chosen) {
      throw lastError || new Error('SKIN_INVALIDA');
    }

    const progression = await secureProgressionState(session.accountId);

    return res.json({
      ok:true,
      reused:!!result?.reused,
      claim:result?.claim || null,
      result:result?.result || chosen,
      progression,
      account:progression?.account || null
    });
  } catch (error) {
    console.error('progression skin roll:', error?.message || error);
    return res.status(409).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/rewards/gift/skin', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) {
    return res.status(401).json({ ok:false, error:'Entre na sua conta para escolher a skin.' });
  }

  const nodeId = String(req.body?.nodeId || '').trim();
  const skinId = sanitizeSkin(req.body?.skinId);
  const node = progressionNodeById(nodeId);

  if (!node || node.reward?.kind !== 'gift') {
    return res.status(404).json({ ok:false, error:'Presente inválido.' });
  }

  try {
    const stateBefore = await loadSecureGameState(session.accountId);
    if (!stateBefore?.wallet) throw new Error('CARTEIRA_NAO_ENCONTRADA');

    const totalXp = totalXpForWallet(stateBefore.wallet);
    if (totalXp < node.xpRequired) {
      throw new Error('XP_INSUFICIENTE');
    }

    const allowed = await dbSelect(SECURE_DB_TABLES.catalog, {
      select:'skin_id,name,rarity,limited,active',
      skin_id:`eq.${skinId}`,
      active:'eq.true',
      limited:'eq.false',
      limit:1
    });

    const skin = allowed[0];
    if (!skin || !['rare','epic'].includes(String(skin.rarity || '')) || COMBO_ONLY_SKIN_IDS.has(String(skin.skin_id || ''))) {
      throw new Error('SKIN_FORA_DA_FAIXA');
    }

    const result = await secureClaimProgressionGiftSkin(session.accountId, node, skin);
    const progression = await secureProgressionState(session.accountId);

    return res.json({
      ok:true,
      reused:!!result?.reused,
      claim:result?.claim || null,
      result:result?.result || skin,
      progression,
      account:progression?.account || null
    });
  } catch (error) {
    console.error('gift skin:', error?.message || error);
    return res.status(409).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/skins/equip', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });

  const skinId = sanitizeSkin(req.body?.skinId);
  try {
    const owned = await dbSelect(SECURE_DB_TABLES.skins, {
      select:'skin_id',
      account_id:`eq.${session.accountId}`,
      skin_id:`eq.${skinId}`,
      limit:1
    });
    if (!owned.length) return res.status(403).json({ ok:false, error:'Você não possui esta skin.' });

    await dbUpdate(
      SECURE_DB_TABLES.accounts,
      { id:`eq.${session.accountId}` },
      { equipped_skin:skinId }
    );
    const state = await loadSecureGameState(session.accountId);
    return res.json({ ok:true, account:secureAccountView(state) });
  } catch (error) {
    console.error('equip:', error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.get('/api/tutorial/status', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });

  try {
    const state = await loadSecureGameState(session.accountId);
    if (!state) return res.status(404).json({ ok:false, error:'Conta não encontrada.' });
    return res.json({
      ok:true,
      tutorialCompleted:tutorialStatusForAccount(state.account) === 'completed',
      tutorialRequired:tutorialIsRequired(state.account),
      tutorialStatus:tutorialStatusForAccount(state.account),
      tutorialBonusClaimed:
        tutorialStatusForAccount(state.account) === 'completed'
        && String(state.account.reward_state || '').toLowerCase() !== 'skipped',
      rewardState:state.account.reward_state,
      reward:state.account.reward_payload,
      googleLinked:!!state.account.google_user_id,
      odds:tutorialOddsPublicView()
    });
  } catch (error) {
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});


/*
   Pular o tutorial é uma decisão permanente para esta conta.
   O servidor grava reward_state='skipped' e tutorial_completed=true.
   Assim:
   - o tutorial não volta a aparecer;
   - nenhuma recompensa de tutorial pode ser obtida depois;
   - não dependemos de localStorage para esta regra.
*/
app.post('/api/tutorial/skip', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) {
    return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });
  }

  const key = `tutorial-skip:${session.accountId}`;
  if (!rateLimit(key, { windowMs:10_000, max:4 })) {
    return res.status(429).json({ ok:false, error:'Aguarde antes de tentar novamente.' });
  }

  try {
    const state = await loadSecureGameState(session.accountId);
    if (!state?.account) {
      return res.status(404).json({ ok:false, error:'Conta não encontrada.' });
    }

    const currentStatus = tutorialStatusForAccount(state.account);

    if (currentStatus === 'completed') {
      return res.json({
        ok:true,
        tutorialStatus:'completed',
        tutorialBonusClaimed:true,
        alreadyFinished:true,
        account:secureAccountView(state)
      });
    }

    if (currentStatus === 'skipped') {
      return res.json({
        ok:true,
        tutorialStatus:'skipped',
        tutorialBonusClaimed:false,
        alreadySkipped:true,
        account:secureAccountView(state)
      });
    }

    await dbUpdate(
      SECURE_DB_TABLES.accounts,
      { id:`eq.${session.accountId}` },
      {
        tutorial_completed:true,
        tutorial_completed_at:new Date().toISOString(),
        reward_state:'skipped',
        reward_payload:null
      }
    );

    const updated = await loadSecureGameState(session.accountId);

    return res.json({
      ok:true,
      tutorialStatus:'skipped',
      tutorialBonusClaimed:false,
      account:secureAccountView(updated)
    });
  } catch (error) {
    console.error('tutorial skip:', error?.message || error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/tutorial/start', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });

  try {
    const state = await loadSecureGameState(session.accountId);
    if (!state) return res.status(404).json({ ok:false, error:'Conta não encontrada.' });
    const tutorialStatus = tutorialStatusForAccount(state.account);

    if (tutorialStatus === 'skipped') {
      return res.status(409).json({
        ok:false,
        code:'TUTORIAL_SKIPPED',
        error:'Este tutorial foi pulado nesta conta e o bônus não está mais disponível.'
      });
    }

    if (tutorialStatus === 'completed') {
      return res.status(409).json({
        ok:false,
        code:'TUTORIAL_ALREADY_COMPLETED',
        error:'Tutorial já concluído.'
      });
    }

    if (!state.account.tutorial_started_at) {
      await dbUpdate(
        SECURE_DB_TABLES.accounts,
        { id:`eq.${session.accountId}` },
        { tutorial_started_at:new Date().toISOString() }
      );
    }
    return res.json({ ok:true });
  } catch (error) {
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/tutorial/reward/select', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });

  const key = `tutorial-select:${session.accountId}`;
  if (!rateLimit(key, { windowMs:60_000, max:6 })) {
    return res.status(429).json({ ok:false, error:'Aguarde antes de tentar novamente.' });
  }

  try {
    const result = await selectTutorialReward(session.accountId, req.body?.cardIndex);
    return res.status(result.status || (result.ok ? 200 : 409)).json(result);
  } catch (error) {
    console.error('tutorial select:', error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/tutorial/reward/roll-skin', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });

  const key = `tutorial-roll:${session.accountId}`;
  if (!rateLimit(key, { windowMs:30_000, max:4 })) {
    return res.status(429).json({ ok:false, error:'A roleta está processando. Aguarde.' });
  }

  try {
    const result = await rollTutorialSkin(session.accountId);
    return res.status(result.status || (result.ok ? 200 : 409)).json(result);
  } catch (error) {
    console.error('tutorial roll:', error);
    return res.status(500).json({ ok:false, error:secureErrorMessage(error) });
  }
});

app.post('/api/tutorial/reward/claim', async (req, res) => {
  const session = sessionFromRequest(req);
  if (!session) return res.status(401).json({ ok:false, error:'Sessão obrigatória.' });

  const key = `tutorial-claim:${session.accountId}`;
  if (!rateLimit(key, { windowMs:10_000, max:4 })) {
    return res.status(429).json({ ok:false, error:'Aguarde o resgate terminar.' });
  }

  try {
    const stateBeforeClaim = await loadSecureGameState(session.accountId);

    if (!stateBeforeClaim?.account) {
      return res.status(404).json({ ok:false, error:'Conta não encontrada.' });
    }

    if (tutorialStatusForAccount(stateBeforeClaim.account) === 'skipped') {
      return res.status(409).json({
        ok:false,
        code:'TUTORIAL_SKIPPED',
        error:'O tutorial foi pulado nesta conta. O bônus não pode mais ser resgatado.'
      });
    }

    const result = await dbRpc('ws_claim_tutorial_reward', {
      p_account_id:session.accountId
    });
    const state = await loadSecureGameState(session.accountId);
    return res.json({ ok:true, claim:result, account:secureAccountView(state) });
  } catch (error) {
    console.error('tutorial claim:', error?.message || error);
    return res.status(409).json({ ok:false, error:secureErrorMessage(error) });
  }
});

/* =========================================================
   V13 - SMTP OPCIONAL PARA RELATÓRIOS
========================================================= */

/*
    Para envio automático real ao Gmail, configure:

    WILDSNAKE_SMTP_USER
    WILDSNAKE_SMTP_APP_PASSWORD

    Exemplo:
    WILDSNAKE_SMTP_USER=seuemail@gmail.com
    WILDSNAKE_SMTP_APP_PASSWORD=xxxx xxxx xxxx xxxx

    Sem essas variáveis, o relatório continua salvo em
    data/wildsnake_state.json e o cliente recebe um mailto
    preenchido como fallback.
*/

const SMTP_USER =
  String(
    process.env.WILDSNAKE_SMTP_USER
    ||
    ''
  )
  .trim();

const SMTP_APP_PASSWORD =
  String(
    process.env.WILDSNAKE_SMTP_APP_PASSWORD
    ||
    ''
  )
  .replace(
    /\s+/g,
    ''
  )
  .trim();


function smtpConfigured(){

  return (
    SMTP_USER.includes(
      '@'
    )
    &&
    SMTP_APP_PASSWORD.length >=
    8
  );

}


function smtpEncodeBase64(
  value
){

  return Buffer.from(
    String(
      value
    ),
    'utf8'
  )
  .toString(
    'base64'
  );

}


function smtpEscapeDots(
  text
){

  return String(
    text
  )
  .replace(
    /\r?\n/g,
    '\r\n'
  )
  .replace(
    /^\./gm,
    '..'
  );

}


function smtpReadResponse(
  socket,
  timeoutMs=8000
){

  return new Promise(
    (
      resolve,
      reject
    )=>{

      let buffer =
        '';

      const timeout =
        setTimeout(
          ()=>{

            cleanup();

            reject(
              new Error(
                'SMTP timeout'
              )
            );

          },
          timeoutMs
        );

      const cleanup =
        ()=>{

          clearTimeout(
            timeout
          );

          socket.off(
            'data',
            onData
          );

          socket.off(
            'error',
            onError
          );

        };

      const onError =
        error=>{

          cleanup();

          reject(
            error
          );

        };

      const onData =
        chunk=>{

          buffer +=
            chunk.toString(
              'utf8'
            );

          const lines =
            buffer
            .split(
              /\r?\n/
            )
            .filter(
              Boolean
            );

          if(
            !lines.length
          ){

            return;

          }

          const last =
            lines[
              lines.length - 1
            ];

          /*
              Resposta SMTP final:
              "250 texto"
              e não
              "250-texto"
          */
          if(
            /^\d{3}\s/.test(
              last
            )
          ){

            cleanup();

            resolve({
              code:
                Number(
                  last.slice(
                    0,
                    3
                  )
                ),

              text:
                buffer
            });

          }

        };

      socket.on(
        'data',
        onData
      );

      socket.on(
        'error',
        onError
      );

    }
  );

}


async function smtpCommand(
  socket,
  command,
  expectedCodes
){

  if(
    command !==
    null
  ){

    socket.write(
      command
      +
      '\r\n'
    );

  }

  const response =
    await smtpReadResponse(
      socket
    );

  const expected =
    Array.isArray(
      expectedCodes
    )
    ?
    expectedCodes
    :
    [
      expectedCodes
    ];

  if(
    !expected.includes(
      response.code
    )
  ){

    throw new Error(
      `SMTP ${response.code}: ${response.text.trim()}`
    );

  }

  return response;

}


async function sendBugReportEmail(
  report
){

  if(
    !smtpConfigured()
  ){

    return {
      ok:false,
      skipped:true,
      reason:'smtp-not-configured'
    };

  }

  const socket =
    tls.connect(
      {
        host:'smtp.gmail.com',
        port:465,
        servername:'smtp.gmail.com',
        rejectUnauthorized:true
      }
    );

  try{

    await new Promise(
      (
        resolve,
        reject
      )=>{

        const timer =
          setTimeout(
            ()=>reject(
              new Error(
                'SMTP connection timeout'
              )
            ),
            9000
          );

        socket.once(
          'secureConnect',
          ()=>{

            clearTimeout(
              timer
            );

            resolve();

          }
        );

        socket.once(
          'error',
          error=>{

            clearTimeout(
              timer
            );

            reject(
              error
            );

          }
        );

      }
    );

    await smtpCommand(
      socket,
      null,
      220
    );

    await smtpCommand(
      socket,
      'EHLO wildsnake.local',
      250
    );

    await smtpCommand(
      socket,
      'AUTH LOGIN',
      334
    );

    await smtpCommand(
      socket,
      smtpEncodeBase64(
        SMTP_USER
      ),
      334
    );

    await smtpCommand(
      socket,
      smtpEncodeBase64(
        SMTP_APP_PASSWORD
      ),
      235
    );

    await smtpCommand(
      socket,
      `MAIL FROM:<${SMTP_USER}>`,
      250
    );

    await smtpCommand(
      socket,
      `RCPT TO:<${BUG_REPORT_EMAIL}>`,
      [
        250,
        251
      ]
    );

    await smtpCommand(
      socket,
      'DATA',
      354
    );

    const subject =
      `[WildSnake ${GAME_VERSION}] Bug ${report.id}`;

    const body =
      [
        `ID: ${report.id}`,
        `Data: ${report.createdAt}`,
        `Versão: ${GAME_VERSION}`,
        `Servidor: ${report.server || '—'}`,
        `Perfil: ${report.profile || 'guest'}`,
        '',
        'Descrição:',
        report.text
      ]
      .join(
        '\r\n'
      );

    const message =
      [
        `From: WildSnake Bug Reporter <${SMTP_USER}>`,
        `To: ${BUG_REPORT_EMAIL}`,
        `Subject: ${subject}`,
        'MIME-Version: 1.0',
        'Content-Type: text/plain; charset=UTF-8',
        'Content-Transfer-Encoding: 8bit',
        '',
        body
      ]
      .join(
        '\r\n'
      );

    socket.write(
      smtpEscapeDots(
        message
      )
      +
      '\r\n.\r\n'
    );

    const accepted =
      await smtpReadResponse(
        socket
      );

    if(
      accepted.code !==
      250
    ){

      throw new Error(
        `SMTP ${accepted.code}`
      );

    }

    try{

      socket.write(
        'QUIT\r\n'
      );

    }
    catch{}

    return {
      ok:true,
      skipped:false
    };

  }
  catch(
    error
  ){

    console.error(
      'Falha SMTP ao enviar bug:',
      error.message
    );

    return {
      ok:false,
      skipped:false,
      reason:
        error.message
    };

  }
  finally{

    try{

      socket.end();

    }
    catch{}

  }

}


/* =========================================================
   V13 - RELATÓRIO DE BUG
========================================================= */

app.post(
  '/api/bug-report',
  async(
    req,
    res
  )=>{

    const key =
      `bug:${req.ip}`;

    if(
      !rateLimit(
        key,
        {
          windowMs:60_000,
          max:6
        }
      )
    ){

      return res.status(
        429
      )
      .json({
        ok:false,
        error:'Muitos relatórios em pouco tempo.'
      });

    }

    const text =
      String(
        req.body?.text
        ||
        ''
      )
      .trim()
      .slice(
        0,
        MAX_BUG_TEXT
      );

    if(
      text.length <
      5
    ){

      return res.status(
        400
      )
      .json({
        ok:false,
        error:'Descreva o problema com um pouco mais de detalhes.'
      });

    }

    const report = {

      id:
        uid(
          'BUG'
        ),

      createdAt:
        new Date().toISOString(),

      text,

      profile:
        String(
          req.body?.profile
          ||
          'guest'
        )
        .slice(
          0,
          100
        ),

      server:
        String(
          req.body?.server
          ||
          ''
        )
        .slice(
          0,
          50
        ),

      version:
        GAME_VERSION,

      userAgent:
        String(
          req.headers['user-agent']
          ||
          ''
        )
        .slice(
          0,
          300
        )

    };

    persistentState.bugReports.unshift(
      report
    );

    if(
      persistentState.bugReports.length >
      500
    ){

      persistentState.bugReports.length =
        500;

    }

    savePersistentState();

    runtimeMetrics.bugReports++;

    const subject =
      encodeURIComponent(
        `[WildSnake ${GAME_VERSION}] Bug ${report.id}`
      );

    const body =
      encodeURIComponent(
        [
          `ID: ${report.id}`,
          `Versão: ${GAME_VERSION}`,
          `Servidor: ${report.server || '—'}`,
          `Perfil: ${report.profile}`,
          '',
          report.text
        ]
        .join(
          '\n'
        )
      );

    const emailResult =
      await sendBugReportEmail(
        report
      );

    res.json({

      ok:true,

      reportId:
        report.id,

      stored:
        true,

      emailConfigured:
        smtpConfigured(),

      emailSent:
        emailResult.ok ===
        true,

      emailError:
        emailResult.ok
        ?
        null
        :
        (
          emailResult.skipped
          ?
          null
          :
          emailResult.reason
        ),

      /*
          Mesmo quando SMTP estiver desligado,
          o cliente recebe um mailto pronto.
      */
      mailto:
        `mailto:${BUG_REPORT_EMAIL}?subject=${subject}&body=${body}`

    });

  }
);


/* =========================================================
   V13 - RUNTIME / DEBUG
========================================================= */

app.get('/api/runtime', (req, res) => {
  res.set('Cache-Control', 'no-store');

  if (!RUNTIME_DEBUG_TOKEN || String(req.headers['x-runtime-token'] || '') !== RUNTIME_DEBUG_TOKEN) {
    return res.status(404).json({ ok:false, error:'Not found' });
  }

  return res.json({
    ok:true,
    version:GAME_VERSION,
    build:BUILD,
    runtime:runtimeSnapshot()
  });
});


/* =========================================================
   HTTP API
========================================================= */

app.get('/api/health', (_req, res) => {
  res.set('Cache-Control','no-store');
  res.set('X-Robots-Tag','noindex, nofollow, noarchive');
  res.type('application/json');
  res.json({
    ok:true,
    game:'WildSnake',
    version:GAME_VERSION,
    build:BUILD,
    secureBackendReady:secureDbReady(),
    googleOAuthReady:googleOAuthReady(),
    configuration:supabaseConfigDiagnostics(),
    now:Date.now()
  });
});

app.get('/api/status', (_req, res) => {
  res.set('Cache-Control','no-store');
  res.set('X-Robots-Tag','noindex, nofollow, noarchive');
  res.type('application/json');
  res.json(buildServerStatusPayload());
});

/* =========================================================
   ROOT / GAME CLIENT
========================================================= */

app.get('/tutorial.html', (req, res) => {
  res.set('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
  res.sendFile(path.join(__dirname, 'Public', 'tutorial.html'));
});

app.get('/', (req, res) => {
  res.set('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
  res.sendFile(
    path.join(
      __dirname,
      'Public',
      'index.html'
    )
  );
});

/* =========================================================
   STATIC / CACHE
========================================================= */

app.use((req, res, next) => {
  if (req.path === '/' || req.path.endsWith('.html')) {
    res.set('Cache-Control', 'no-store, no-cache, must-revalidate, proxy-revalidate');
  }
  next();
});

app.use(express.static(path.join(__dirname, 'Public')));

/* =========================================================
   SERVER ERRORS
========================================================= */

httpServer.on('error', error => {
  console.error('\n❌ ERRO AO INICIAR SERVIDOR:', error.message);

  if (error.code === 'EADDRINUSE') {
    console.error(`A porta ${PORT} já está ocupada. Feche o outro processo Node antes de iniciar.`);
  }
});

process.on('uncaughtException', error => {
  console.error('❌ uncaughtException:', error);
});

process.on('unhandledRejection', error => {
  console.error('❌ unhandledRejection:', error);
});

/* =========================================================
   START
========================================================= */

httpServer.listen(PORT, '0.0.0.0', () => {
  console.log('\n============================================================');
  console.log(`🐍 WILDSNAKE ONLINE ${GAME_VERSION}`);
  console.log(`🔧 BUILD: ${BUILD}`);
  console.log(`🌐 http://localhost:${PORT}`);
  console.log(`🔐 Secure backend: ${secureDbReady() ? 'READY' : 'FALTAM VARIÁVEIS SUPABASE'}`);
  if (!secureDbReady()) {
    console.log('⚠️  Configuração ausente:', supabaseConfigDiagnostics().missing.join(', ') || 'desconhecida');
  }
  console.log(`❤️  http://localhost:${PORT}/api/health`);
  console.log('✅ Rota / entrega Public/index.html explicitamente');
  console.log('✅ Multi-servidor: BR / US / EU / AS');
  console.log('✅ JOGAR AGORA escolhe automaticamente uma arena pública');
  console.log('✅ Lista manual de servidores via /api/status');
  console.log('✅ Comida online: pública + privada');
  console.log('✅ Comida de morte: ATIVA');
  console.log('✅ Bots adaptativos: ATIVOS quando há poucos humanos');
  console.log('✅ Bots com nomes naturais: ATIVO');
  console.log('✅ Colisão autoritativa contínua + anti-tunneling reforçado');
  console.log('✅ Corpo autoritativo enviado ao cliente');
  console.log('✅ Líder calculado no servidor por COMIDAS');
  console.log('✅ Status das arenas enviado pelo backend a cada 3 segundos sem piscar a interface');
  console.log(`✅ Google OAuth backend: ${googleOAuthReady() ? 'READY' : 'AGUARDANDO CONFIGURAÇÃO'}`);
  console.log('✅ WildCoins: 3 comidas = 1 moeda');
  console.log('✅ Modal solo + esperar + trocar servidor + sair');
  console.log('✅ Sala privada + lobby + pronto + bots + respawn');
  console.log(`✅ Rede: ${WORLD_BROADCAST_RATE} world/s + ${FOOD_BROADCAST_RATE} food/s`);
  console.log('============================================================\n');
});
