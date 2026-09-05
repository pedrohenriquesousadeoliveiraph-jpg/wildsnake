const express = require('express');
const http = require('http');
const path = require('path');
const fs = require('fs');
const os = require('os');
const tls = require('tls');
const crypto = require('crypto');
const { Server } = require('socket.io');

const app = express();

app.disable('x-powered-by');
app.use(express.json({ limit: '256kb' }));

const httpServer = http.createServer(app);
const io = new Server(httpServer, {
  cors: { origin: '*', methods: ['GET', 'POST'] },
  transports: ['websocket', 'polling'],
  pingInterval: 10000,
  pingTimeout: 8000,
  connectTimeout: 12000,
  maxHttpBufferSize: 1e6
});

/* =========================================================
   WILDSNAKE SERVER CONFIG
========================================================= */

const PORT = Number(process.env.PORT || 3000);
const GAME_VERSION = 'v13.00.2';
const BUILD = 'wildsnake-v13.00.2-render-auth-online';

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
const MAX_ROOM_PLAYERS = 24;
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
  6;

const sessions =
  new Map();

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


function createSession(
  accountId,
  role='player'
){

  const token =
    crypto.randomBytes(
      32
    )
    .toString(
      'hex'
    );

  const now =
    Date.now();

  sessions.set(
    token,
    {

      token,

      accountId,

      role,

      createdAt:
        now,

      expiresAt:
        now
        +
        SESSION_TTL_MS

    }
  );

  return token;

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

  const token =
    readBearerToken(
      req
    );

  if(
    !token
  ){

    return null;

  }

  const session =
    sessions.get(
      token
    );

  if(
    !session
  ){

    return null;

  }

  if(
    Date.now() >
    session.expiresAt
  ){

    sessions.delete(
      token
    );

    return null;

  }

  return session;

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
   V13 - PERFIL DE DESEMPENHO / REDE ADAPTATIVA
========================================================= */

const NETWORK_PROFILES = {

  weak:{
    id:'weak',
    worldHz:6,
    segmentLimit:28,
    foodHz:1,
    interpolationHint:0.18
  },

  medium:{
    id:'medium',
    worldHz:9,
    segmentLimit:46,
    foodHz:2,
    interpolationHint:0.13
  },

  strong:{
    id:'strong',
    worldHz:12,
    segmentLimit:70,
    foodHz:2,
    interpolationHint:0.09
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
  player
){

  return NETWORK_PROFILES[
    normalizePerformanceTier(
      player.performanceTier
    )
  ];

}


function sampleBodyForNetwork(
  snake,
  limit
){

  const body =
    bodySegments(
      snake,
      0
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
  'unicorn'
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

  snake.prevBodySegments =
    bodySegments(
      snake,
      0
    )
    .map(
      point => ({
        x: point.x,
        y: point.y
      })
    );
}

function updateTrail(snake) {
  snake.trail.unshift({
    x: snake.x,
    y: snake.y
  });

  const maxTrail =
    Math.max(
      220,
      Math.ceil(
        snake.length
        *
        SEGMENT_SPACING
        /
        3
      )
      +
      130
    );

  if (
    snake.trail.length >
    maxTrail
  ) {
    snake.trail.length =
      maxTrail;
  }
}

function bodySegments(
  snake,
  offset = 0
) {
  if (
    !Array.isArray(
      snake.trail
    )
    ||
    snake.trail.length === 0
  ) {
    return [];
  }

  const count =
    Math.max(
      8,
      Math.floor(
        snake.length
      )
    );

  const result =
    [];

  for (
    let i = 0;
    i < count;
    i++
  ) {
    const index =
      Math.min(
        snake.trail.length - 1,
        offset
        +
        Math.floor(
          i
          *
          SEGMENT_SPACING
          /
          3
        )
      );

    const point =
      snake.trail[
        index
      ];

    if (point) {
      result.push(
        point
      );
    }
  }

  return result;
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
    performanceTier: 'medium',
    performanceInfo: null,
    lastWorldSentAt: 0,
    lastFoodSentAt: 0,
    socketSequence: 0,
    profileId: null
  };
}

function prepareSnake(
  snake,
  room
) {
  const spawn =
    findSpawn(
      room
    );

  snake.x =
    spawn.x;

  snake.y =
    spawn.y;

  snake.prevX =
    spawn.x;

  snake.prevY =
    spawn.y;

  snake.angle =
    rand(
      -Math.PI,
      Math.PI
    );

  snake.targetAngle =
    snake.angle;

  snake.boost =
    false;

  snake.length =
    18;

  snake.score =
    0;

  snake.kills =
    0;

  snake.alive =
    true;

  snake.startedAt =
    Date.now();

  snake.respawnAt =
    0;

  snake.lastInput =
    Date.now();

  snake.waitingSolo =
    false;

  snake.pendingPublicResume =
    false;

  snake.inArena =
    true;

  seedTrail(
    snake
  );
}

function currentLeaderId(room) {
  const alive =
    activeRoomSnakes(
      room
    )
    .filter(
      snake =>
        !snake.waitingSolo
        &&
        snake.inArena !== false
    );

  if (!alive.length) {
    return null;
  }

  alive.sort(
    (a, b) =>
      (b.score || 0)
      -
      (a.score || 0)

      ||

      (b.length || 0)
      -
      (a.length || 0)

      ||

      (b.kills || 0)
      -
      (a.kills || 0)

      ||

      String(a.id)
        .localeCompare(
          String(b.id)
        )
  );

  return alive[0].id;
}

function serializePlayer(
  snake,
  leaderId = null,
  segmentLimit = 70
) {
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
    kills: snake.kills || 0,
    alive: !!snake.alive,
    isBot: !!snake.isBot,
    isLeader:
      snake.id === leaderId,

    segments:
      sampleBodyForNetwork(
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
    total:
      room.players.size
      +
      room.botIds.size,

    active:
      room.players.size > 0,

    waitingForPlayers:
      room.waitingForPlayers,

    max:
      MAX_ROOM_PLAYERS,

    leaderId:
      room.leaderId,

    version:
      GAME_VERSION
  };
}

/* =========================================================
   BOTS
========================================================= */

function uniqueBotName(
  room,
  index
) {
  const used =
    new Set(
      roomSnakes(
        room
      )
      .map(
        snake =>
          snake.name
      )
    );

  for (
    let offset = 0;
    offset < BOT_NAMES.length;
    offset++
  ) {
    const name =
      BOT_NAMES[
        (
          index
          +
          offset
        )
        %
        BOT_NAMES.length
      ];

    if (
      !used.has(
        name
      )
    ) {
      return name;
    }
  }

  return (
    `Wild${Math.floor(rand(100,999))}`
  );
}

function createBot(
  room,
  index
) {
  const bot = {
    id:
      uid(
        'BOT'
      ),

    name:
      uniqueBotName(
        room,
        index
      ),

    skinId:
      BOT_SKINS[
        index
        %
        BOT_SKINS.length
      ],

    color:
      BOT_COLORS[
        index
        %
        BOT_COLORS.length
      ],

    roomId:
      room.code,

    roomType:
      room.type,

    ready:
      true,

    alive:
      false,

    isBot:
      true,

    x:
      0,

    y:
      0,

    prevX:
      0,

    prevY:
      0,

    angle:
      0,

    targetAngle:
      0,

    speed:
      BASE_SPEED
      *
      rand(
        0.92,
        1.02
      ),

    boost:
      false,

    length:
      rand(
        17,
        24
      ),

    score:
      Math.floor(
        rand(
          0,
          40
        )
      ),

    kills:
      0,

    trail:
      [],

    prevBodySegments:
      [],

    aiTimer:
      rand(
        0.45,
        1.15
      ),

    mistake:
      rand(
        0.18,
        0.36
      ),

    aggression:
      rand(
        0.12,
        0.34
      ),

    lastInput:
      Date.now(),

    startedAt:
      0,

    respawnAt:
      0,

    waitingSolo:
      false,

    pendingPublicResume:
      false,

    inArena:
      true
  };

  players.set(
    bot.id,
    bot
  );

  room.botIds.add(
    bot.id
  );

  prepareSnake(
    bot,
    room
  );

  bot.length =
    rand(
      17,
      24
    );

  return bot;
}

function removeBot(
  room,
  id
) {
  room.botIds.delete(
    id
  );

  players.delete(
    id
  );
}

function removeAllBots(
  room
) {
  for (
    const id
    of
    [
      ...room.botIds
    ]
  ) {
    removeBot(
      room,
      id
    );
  }
}

/*
  Regras:
  - abaixo de 7 humanos SEMPRE há bots;
  - 8/9 humanos ainda ficam com poucos bots;
  - quanto mais humanos, menos IA.
*/

function desiredPublicBots(
  humans
) {
  if (
    humans <= 1
  ) {
    return 10;
  }

  if (
    humans <= 2
  ) {
    return 9;
  }

  if (
    humans <= 4
  ) {
    return 7;
  }

  if (
    humans <= 6
  ) {
    return 5;
  }

  if (
    humans <= 9
  ) {
    return 4;
  }

  if (
    humans <= 12
  ) {
    return 2;
  }

  return 0;
}

function rebalancePublicBots(
  room
) {
  if (
    !room
    ||
    room.type !==
    'public'
  ) {
    return;
  }

  const humans =
    room.players.size;

  if (
    humans === 0
  ) {
    removeAllBots(
      room
    );

    room.foods.clear();

    room.active =
      false;

    room.waitingForPlayers =
      false;

    room.soloSince =
      0;

    room.lastHumanCount =
      0;

    room.leaderId =
      null;

    return;
  }

  room.active =
    true;

  ensureFood(
    room
  );

  const desired =
    desiredPublicBots(
      humans
    );

  const current =
    room.botIds.size;

  if (
    current <
    desired
  ) {
    for (
      let i = current;
      i < desired;
      i++
    ) {
      createBot(
        room,
        i
      );
    }
  }
  else if (
    current >
    desired
  ) {
    const ids =
      [
        ...room.botIds
      ];

    for (
      let i = 0;
      i < current - desired;
      i++
    ) {
      removeBot(
        room,
        ids[i]
      );
    }
  }
}

function rebalanceAllPublicBots() {
  for (
    const room
    of
    publicRooms.values()
  ) {
    rebalancePublicBots(
      room
    );
  }
}

/* =========================================================
   PRIVATE LOBBY
========================================================= */

function serializeLobby(
  room
) {
  const list =
    roomHumans(
      room
    )
    .map(
      player => ({
        id: player.id,
        name: player.name,
        skinId: player.skinId,
        ready: !!player.ready,
        host:
          room.hostId ===
          player.id,

        alive:
          !!player.alive,

        inArena:
          player.inArena !== false,

        spectating:
          room.started
          &&
          player.inArena === false
      })
    );

  const readyCount =
    list.filter(
      player =>
        player.ready
    )
    .length;

  const minimumReady =
    room.botsEnabled
    &&
    room.botCount > 0
    ?
    1
    :
    2;

  return {
    code:
      room.code,

    name:
      room.name,

    hostId:
      room.hostId,

    started:
      room.started,

    botsEnabled:
      room.botsEnabled,

    botCount:
      room.botCount,

    players:
      list,

    onlineCount:
      list.length,

    readyCount,

    minimumReady,

    canStart:
      !room.started
      &&
      list.length >=
      minimumReady
      &&
      readyCount ===
      list.length,

    version:
      GAME_VERSION
  };
}

function emitLobby(
  room
) {
  const state =
    serializeLobby(
      room
    );

  io.to(
    room.code
  )
  .emit(
    'lobbyState',
    state
  );

  return state;
}

/* =========================================================
   ROOM DETACH
========================================================= */

function detachPlayerFromRoom(
  player,
  {
    emitLobbyState = true
  } = {}
) {
  if (
    !player
    ||
    !player.roomId
  ) {
    return null;
  }

  const room =
    getRoom(
      player.roomId
    );

  const oldRoomId =
    player.roomId;

  if (room) {
    room.players.delete(
      player.id
    );

    if (
      room.type ===
      'private'
    ) {
      if (
        room.players.size === 0
      ) {
        removeAllBots(
          room
        );

        room.foods.clear();

        privateRooms.delete(
          room.code
        );
      }
      else {
        if (
          room.hostId ===
          player.id
        ) {
          room.hostId =
            [
              ...room.players
            ][0];
        }

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
    }
    else {
      rebalancePublicBots(
        room
      );

      updatePublicSoloState(
        room,
        true
      );
    }
  }

  const socket =
    io.sockets.sockets.get(
      player.id
    );

  if (socket) {
    socket.leave(
      oldRoomId
    );
  }

  player.roomId =
    null;

  player.roomType =
    null;

  player.ready =
    false;

  player.alive =
    false;

  player.boost =
    false;

  player.waitingSolo =
    false;

  player.pendingPublicResume =
    false;

  player.inArena =
    false;

  return room;
}

/* =========================================================
   GEOMETRY
========================================================= */

function pointSeg(
  px,
  py,
  ax,
  ay,
  bx,
  by
) {
  const abx =
    bx - ax;

  const aby =
    by - ay;

  const den =
    abx * abx
    +
    aby * aby;

  if (
    den < 1e-9
  ) {
    return Math.hypot(
      px - ax,
      py - ay
    );
  }

  const t =
    clamp(
      (
        (px - ax)
        *
        abx

        +

        (py - ay)
        *
        aby
      )
      /
      den,
      0,
      1
    );

  const cx =
    ax
    +
    abx
    *
    t;

  const cy =
    ay
    +
    aby
    *
    t;

  return Math.hypot(
    px - cx,
    py - cy
  );
}

function orientation(
  ax,
  ay,
  bx,
  by,
  cx,
  cy
) {
  const value =
    (by - ay)
    *
    (cx - bx)
    -
    (bx - ax)
    *
    (cy - by);

  if (
    Math.abs(
      value
    )
    <
    1e-9
  ) {
    return 0;
  }

  return (
    value > 0
    ?
    1
    :
    2
  );
}

function onSegment(
  ax,
  ay,
  bx,
  by,
  cx,
  cy
) {
  return (
    bx <=
    Math.max(
      ax,
      cx
    )
    +
    1e-9

    &&

    bx + 1e-9 >=
    Math.min(
      ax,
      cx
    )

    &&

    by <=
    Math.max(
      ay,
      cy
    )
    +
    1e-9

    &&

    by + 1e-9 >=
    Math.min(
      ay,
      cy
    )
  );
}

function segmentsIntersect(
  ax,
  ay,
  bx,
  by,
  cx,
  cy,
  dx,
  dy
) {
  const o1 =
    orientation(
      ax,
      ay,
      bx,
      by,
      cx,
      cy
    );

  const o2 =
    orientation(
      ax,
      ay,
      bx,
      by,
      dx,
      dy
    );

  const o3 =
    orientation(
      cx,
      cy,
      dx,
      dy,
      ax,
      ay
    );

  const o4 =
    orientation(
      cx,
      cy,
      dx,
      dy,
      bx,
      by
    );

  if (
    o1 !== o2
    &&
    o3 !== o4
  ) {
    return true;
  }

  if (
    o1 === 0
    &&
    onSegment(
      ax,
      ay,
      cx,
      cy,
      bx,
      by
    )
  ) {
    return true;
  }

  if (
    o2 === 0
    &&
    onSegment(
      ax,
      ay,
      dx,
      dy,
      bx,
      by
    )
  ) {
    return true;
  }

  if (
    o3 === 0
    &&
    onSegment(
      cx,
      cy,
      ax,
      ay,
      dx,
      dy
    )
  ) {
    return true;
  }

  if (
    o4 === 0
    &&
    onSegment(
      cx,
      cy,
      bx,
      by,
      dx,
      dy
    )
  ) {
    return true;
  }

  return false;
}

function segSeg(
  ax,
  ay,
  bx,
  by,
  cx,
  cy,
  dx,
  dy
) {
  if (
    segmentsIntersect(
      ax,
      ay,
      bx,
      by,
      cx,
      cy,
      dx,
      dy
    )
  ) {
    return 0;
  }

  return Math.min(
    pointSeg(
      ax,
      ay,
      cx,
      cy,
      dx,
      dy
    ),

    pointSeg(
      bx,
      by,
      cx,
      cy,
      dx,
      dy
    ),

    pointSeg(
      cx,
      cy,
      ax,
      ay,
      bx,
      by
    ),

    pointSeg(
      dx,
      dy,
      ax,
      ay,
      bx,
      by
    )
  );
}

function sweptHeads(
  a,
  b
) {
  const r0x =
    a.prevX -
    b.prevX;

  const r0y =
    a.prevY -
    b.prevY;

  const drx =
    (a.x - a.prevX)
    -
    (b.x - b.prevX);

  const dry =
    (a.y - a.prevY)
    -
    (b.y - b.prevY);

  const den =
    drx * drx
    +
    dry * dry;

  const t =
    den > 1e-9
    ?
    clamp(
      -(
        r0x * drx
        +
        r0y * dry
      )
      /
      den,
      0,
      1
    )
    :
    0;

  return Math.hypot(
    r0x +
    drx * t,

    r0y +
    dry * t
  );
}

function sweptHeadAgainstBody(
  attacker,
  defender
) {
  const current =
    bodySegments(
      defender,
      0
    );

  const previous =
    Array.isArray(
      defender.prevBodySegments
    )
    &&
    defender.prevBodySegments.length
    ?
    defender.prevBodySegments
    :
    bodySegments(
      defender,
      1
    );

  if (
    current.length <
    4
  ) {
    return Infinity;
  }

  let best =
    Infinity;

  for (
    let i = 2;
    i < current.length - 1;
    i++
  ) {
    const c1 =
      current[i];

    const c2 =
      current[
        i + 1
      ];

    if (
      !c1
      ||
      !c2
    ) {
      continue;
    }

    best =
      Math.min(
        best,
        segSeg(
          attacker.prevX,
          attacker.prevY,
          attacker.x,
          attacker.y,
          c1.x,
          c1.y,
          c2.x,
          c2.y
        )
      );

    const p1 =
      previous[i];

    const p2 =
      previous[
        i + 1
      ];

    if (
      p1
      &&
      p2
    ) {
      best =
        Math.min(
          best,
          segSeg(
            attacker.prevX,
            attacker.prevY,
            attacker.x,
            attacker.y,
            p1.x,
            p1.y,
            p2.x,
            p2.y
          )
        );

      best =
        Math.min(
          best,
          segSeg(
            attacker.prevX,
            attacker.prevY,
            attacker.x,
            attacker.y,
            p1.x,
            p1.y,
            c1.x,
            c1.y
          )
        );

      best =
        Math.min(
          best,
          segSeg(
            attacker.prevX,
            attacker.prevY,
            attacker.x,
            attacker.y,
            p2.x,
            p2.y,
            c2.x,
            c2.y
          )
        );
    }

    if (
      best <=
      HEAD_BODY_DISTANCE
    ) {
      return best;
    }
  }

  return best;
}

/* =========================================================
   DEATH / DROP FOOD
========================================================= */

function scatterDeathFood(
  room,
  snake
) {
  const body =
    bodySegments(
      snake,
      0
    );

  for (
    let i = 1;
    i < body.length;
    i += 2
  ) {
    if (
      room.foods.size >=
      FOOD_HARD_LIMIT
    ) {
      break;
    }

    spawnFood(
      room,

      body[i].x
      +
      rand(
        -10,
        10
      ),

      body[i].y
      +
      rand(
        -10,
        10
      ),

      Math.max(
        1,
        Math.min(
          8,
          Math.floor(
            (snake.score || 1)
            /
            Math.max(
              1,
              body.length / 2
            )
            /
            3
          )
          ||
          1
        )
      ),

      snake.color
    );
  }
}

function killSnake(
  room,
  snake,
  reason,
  killer = null
) {
  if (
    !snake
    ||
    !snake.alive
  ) {
    return;
  }

  snake.alive =
    false;

  runtimeMetrics.deaths++;

  snake.boost =
    false;

  scatterDeathFood(
    room,
    snake
  );

  if (
    killer
    &&
    killer !== snake
    &&
    killer.alive
  ) {
    killer.kills =
      (killer.kills || 0)
      +
      1;

    killer.score =
      (killer.score || 0)
      +
      25;
  }

  if (
    snake.isBot
  ) {
    snake.respawnAt =
      Date.now()
      +
      rand(
        1800,
        3200
      );

    return;
  }

  snake.inArena =
    false;

  const socket =
    io.sockets.sockets.get(
      snake.id
    );

  if (socket) {
    socket.emit(
      'playerDied',
      {
        reason,

        score:
          Math.floor(
            snake.score || 0
          ),

        kills:
          snake.kills || 0,

        length:
          Number(
            (snake.length || 18)
            .toFixed(
              1
            )
          ),

        timeMs:
          Math.max(
            0,
            Date.now()
            -
            (
              snake.startedAt
              ||
              Date.now()
            )
          ),

        roomId:
          room.code,

        privateRoom:
          room.type ===
          'private',

        version:
          GAME_VERSION
      }
    );
  }

  if (
    room.type ===
    'private'
  ) {
    emitLobby(
      room
    );
  }
}

/* =========================================================
   MOVEMENT
========================================================= */

function moveSnake(
  snake,
  dt,
  turnSpeed = 3.2
) {
  snake.prevBodySegments =
    bodySegments(
      snake,
      0
    )
    .map(
      point => ({
        x: point.x,
        y: point.y
      })
    );

  const difference =
    Math.atan2(
      Math.sin(
        snake.targetAngle
        -
        snake.angle
      ),
      Math.cos(
        snake.targetAngle
        -
        snake.angle
      )
    );

  snake.angle =
    norm(
      snake.angle
      +
      clamp(
        difference,
        -turnSpeed * dt,
        turnSpeed * dt
      )
    );

  let speed =
    snake.speed;

  if (
    snake.boost
    &&
    snake.length >
    MIN_LENGTH
  ) {
    speed *=
      BOOST_MULT;

    snake.length =
      Math.max(
        MIN_LENGTH,
        snake.length
        -
        0.32 * dt
      );
  }

  snake.prevX =
    snake.x;

  snake.prevY =
    snake.y;

  snake.x +=
    Math.cos(
      snake.angle
    )
    *
    speed
    *
    dt;

  snake.y +=
    Math.sin(
      snake.angle
    )
    *
    speed
    *
    dt;

  updateTrail(
    snake
  );
}

/* =========================================================
   BOT AI
========================================================= */

function nearestFood(
  room,
  bot,
  maxDistance = 850
) {
  let best =
    null;

  let bestDistance =
    maxDistance;

  for (
    const food
    of
    room.foods.values()
  ) {
    const distance =
      Math.hypot(
        food.x - bot.x,
        food.y - bot.y
      );

    if (
      distance <
      bestDistance
    ) {
      bestDistance =
        distance;

      best =
        food;
    }
  }

  return best;
}

function nearestHuman(
  room,
  bot,
  maxDistance = 900
) {
  let best =
    null;

  let bestDistance =
    maxDistance;

  for (
    const human
    of
    roomHumans(
      room
    )
  ) {
    if (
      !human.alive
      ||
      human.waitingSolo
    ) {
      continue;
    }

    const distance =
      Math.hypot(
        human.x - bot.x,
        human.y - bot.y
      );

    if (
      distance <
      bestDistance
    ) {
      bestDistance =
        distance;

      best =
        human;
    }
  }

  return best;
}

function updateBot(
  room,
  bot,
  dt
) {
  if (
    !bot.alive
  ) {
    if (
      bot.respawnAt
      &&
      Date.now() >=
      bot.respawnAt
    ) {
      prepareSnake(
        bot,
        room
      );
    }

    return;
  }

  bot.aiTimer -=
    dt;

  if (
    bot.aiTimer <= 0
  ) {
    bot.aiTimer =
      rand(
        0.48,
        1.15
      );

    const center =
      Math.hypot(
        bot.x,
        bot.y
      );

    const food =
      nearestFood(
        room,
        bot
      );

    const human =
      nearestHuman(
        room,
        bot
      );

    if (
      center >
      SAFE_RADIUS - 520
    ) {
      bot.targetAngle =
        Math.atan2(
          -bot.y,
          -bot.x
        )
        +
        rand(
          -0.28,
          0.28
        );
    }
    else if (
      Math.random() <
      bot.mistake
    ) {
      bot.targetAngle =
        norm(
          bot.angle
          +
          rand(
            -1.5,
            1.5
          )
        );
    }
    else if (
      human
      &&
      Math.random() <
      bot.aggression
    ) {
      bot.targetAngle =
        Math.atan2(
          human.y - bot.y,
          human.x - bot.x
        )
        +
        rand(
          -0.26,
          0.26
        );
    }
    else if (food) {
      bot.targetAngle =
        Math.atan2(
          food.y - bot.y,
          food.x - bot.x
        )
        +
        rand(
          -0.22,
          0.22
        );
    }
    else {
      bot.targetAngle =
        norm(
          bot.angle
          +
          rand(
            -0.85,
            0.85
          )
        );
    }

    bot.boost =
      bot.length > 20
      &&
      Math.random() < 0.06;
  }

  moveSnake(
    bot,
    dt,
    2.15
  );
}

/* =========================================================
   FOOD COLLISION
========================================================= */

function eatFood(
  room,
  snake
) {
  let eaten =
    0;

  for (
    const [
      id,
      food
    ]
    of
    room.foods
  ) {
    if (
      Math.hypot(
        snake.x - food.x,
        snake.y - food.y
      )
      <
      HEAD_RADIUS
      +
      food.r
      +
      4
    ) {
      room.foods.delete(
        id
      );

      room.foodRevision =
        (room.foodRevision || 0)
        +
        1;

      snake.score +=
        food.value;

      snake.length +=
        food.value
        *
        0.11;

      eaten++;

      if (
        eaten >= 3
      ) {
        break;
      }
    }
  }
}

/* =========================================================
   COLLISIONS
========================================================= */

function handleCollisions(
  room
) {
  let alive =
    activeRoomSnakes(
      room
    )
    .filter(
      snake =>
        !snake.waitingSolo
        &&
        snake.inArena !== false
    );

  for (
    const snake
    of
    alive
  ) {
    if (
      Math.hypot(
        snake.x,
        snake.y
      )
      >
      SAFE_RADIUS
    ) {
      killSnake(
        room,
        snake,
        'Você saiu da área segura.'
      );
    }
  }

  alive =
    activeRoomSnakes(
      room
    )
    .filter(
      snake =>
        !snake.waitingSolo
        &&
        snake.inArena !== false
    );

  for (
    let i = 0;
    i < alive.length;
    i++
  ) {
    const a =
      alive[i];

    if (
      !a.alive
    ) {
      continue;
    }

    for (
      let j = i + 1;
      j < alive.length;
      j++
    ) {
      const b =
        alive[j];

      if (
        !b.alive
      ) {
        continue;
      }

      const currentDistance =
        Math.hypot(
          a.x - b.x,
          a.y - b.y
        );

      const sweptDistance =
        sweptHeads(
          a,
          b
        );

      if (
        currentDistance <=
        HEAD_HEAD_DISTANCE
        ||
        sweptDistance <=
        HEAD_HEAD_DISTANCE
      ) {
        killSnake(
          room,
          a,
          `Cabeça com cabeça com ${b.name}.`
        );

        killSnake(
          room,
          b,
          `Cabeça com cabeça com ${a.name}.`
        );
      }
    }
  }

  alive =
    activeRoomSnakes(
      room
    )
    .filter(
      snake =>
        !snake.waitingSolo
        &&
        snake.inArena !== false
    );

  for (
    const attacker
    of
    alive
  ) {
    if (
      !attacker.alive
    ) {
      continue;
    }

    for (
      const defender
      of
      alive
    ) {
      if (
        attacker === defender
        ||
        !attacker.alive
        ||
        !defender.alive
      ) {
        continue;
      }

      const distance =
        sweptHeadAgainstBody(
          attacker,
          defender
        );

      if (
        distance <=
        HEAD_BODY_DISTANCE
      ) {
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

function updateRoom(
  room,
  dt
) {
  if (
    !room.started
  ) {
    return;
  }

  for (
    const snake
    of
    roomSnakes(
      room
    )
  ) {
    if (
      snake.isBot
    ) {
      updateBot(
        room,
        snake,
        dt
      );
    }
    else if (
      snake.alive
      &&
      !snake.waitingSolo
      &&
      snake.inArena !== false
    ) {
      if (
        Date.now()
        -
        snake.lastInput
        >
        HUMAN_INPUT_TIMEOUT_MS
      ) {
        snake.boost =
          false;
      }

      moveSnake(
        snake,
        dt,
        3.2
      );
    }

    if (
      snake.alive
      &&
      !snake.waitingSolo
      &&
      snake.inArena !== false
    ) {
      eatFood(
        room,
        snake
      );
    }
  }

  handleCollisions(
    room
  );

  ensureFood(
    room
  );

  room.leaderId =
    currentLeaderId(
      room
    );
}

/* =========================================================
   WORLD / FOOD BROADCAST
========================================================= */

function emitWorld(
  room
) {
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

  for (
    const receiver
    of
    roomHumans(
      room
    )
  ) {
    const socket =
      io.sockets.sockets.get(
        receiver.id
      );

    if (
      !socket
      ||
      !socket.connected
    ) {
      continue;
    }

    const profile =
      networkProfileForPlayer(
        receiver
      );

    const interval =
      1000
      /
      profile.worldHz;

    if (
      now
      -
      (
        receiver.lastWorldSentAt
        ||
        0
      )
      <
      interval - 2
    ) {
      continue;
    }

    receiver.lastWorldSentAt =
      now;

    receiver.socketSequence =
      (receiver.socketSequence || 0)
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

    socket.emit(
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
          snakes.map(
            snake =>
              serializePlayer(
                snake,
                leaderId,
                profile.segmentLimit
              )
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
) {
  const buildPayload =
    () => ({
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

  if (socket) {
    socket.emit(
      'foodState',
      buildPayload()
    );

    runtimeMetrics.foodPackets++;

    return;
  }

  const now =
    Date.now();

  for (
    const receiver
    of
    roomHumans(
      room
    )
  ) {
    const receiverSocket =
      io.sockets.sockets.get(
        receiver.id
      );

    if (
      !receiverSocket
      ||
      !receiverSocket.connected
    ) {
      continue;
    }

    const profile =
      networkProfileForPlayer(
        receiver
      );

    const interval =
      1000
      /
      profile.foodHz;

    if (
      !force
      &&
      now
      -
      (
        receiver.lastFoodSentAt
        ||
        0
      )
      <
      interval - 4
    ) {
      continue;
    }

    receiver.lastFoodSentAt =
      now;

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

function chooseAutoPublicServer(
  excludeId = null
) {
  const all =
    [
      ...publicRooms.values()
    ]
    .filter(
      room =>
        room.code !==
        excludeId
        &&
        room.players.size <
        MAX_ROOM_PLAYERS
    );

  const occupied =
    all.filter(
      room =>
        room.players.size > 0
    );

  const pool =
    occupied.length
    ?
    occupied
    :
    all;

  pool.sort(
    (a, b) =>
      a.players.size
      -
      b.players.size
      ||
      a.botIds.size
      -
      b.botIds.size
      ||
      a.code.localeCompare(
        b.code
      )
  );

  return (
    pool[0]
    ||
    null
  );
}

function chooseAlternativePublicServer(
  currentId
) {
  const rooms =
    [
      ...publicRooms.values()
    ]
    .filter(
      room =>
        room.code !==
        currentId
        &&
        room.players.size > 0
        &&
        room.players.size <
        MAX_ROOM_PLAYERS
    );

  rooms.sort(
    (a, b) =>
      a.players.size
      -
      b.players.size
      ||
      a.code.localeCompare(
        b.code
      )
  );

  return (
    rooms[0]
    ||
    null
  );
}

/* =========================================================
   JOIN PUBLIC
========================================================= */

function joinPublicRoom(
  socket,
  player,
  room
) {
  detachPlayerFromRoom(
    player
  );

  player.roomId =
    room.code;

  player.roomType =
    'public';

  player.ready =
    true;

  player.waitingSolo =
    false;

  player.pendingPublicResume =
    false;

  room.players.add(
    player.id
  );

  room.active =
    true;

  socket.join(
    room.code
  );

  prepareSnake(
    player,
    room
  );

  ensureFood(
    room
  );

  rebalancePublicBots(
    room
  );

  updatePublicSoloState(
    room,
    true
  );

  const payload = {
    ok:
      true,

    mode:
      'public',

    roomId:
      room.code,

    server:
      serializePublicRoom(
        room
      ),

    version:
      GAME_VERSION,

    player:
      serializePlayer(
        player,
        currentLeaderId(
          room
        )
      ),

    worldRadius:
      WORLD_RADIUS
  };

  emitFoods(
    room,
    socket
  );

  return payload;
}

/* =========================================================
   SOLO PUBLIC STATE
========================================================= */

function updatePublicSoloState(
  room,
  force = false
) {
  if (
    !room
    ||
    room.type !==
    'public'
  ) {
    return;
  }

  const humans =
    roomHumans(
      room
    );

  const count =
    humans.length;

  const now =
    Date.now();

  if (
    count === 0
  ) {
    room.waitingForPlayers =
      false;

    room.soloSince =
      0;

    room.lastHumanCount =
      0;

    room.soloNoticeSent =
      false;

    return;
  }

  if (
    count >= 2
  ) {
    const waiting =
      humans.filter(
        player =>
          player.waitingSolo
          ||
          player.pendingPublicResume
      );

    room.waitingForPlayers =
      false;

    room.soloSince =
      0;

    room.soloNoticeSent =
      false;

    for (
      const player
      of
      waiting
    ) {
      player.pendingPublicResume =
        true;

      const socket =
        io.sockets.sockets.get(
          player.id
        );

      if (socket) {
        socket.emit(
          'publicMatchFound',
          {
            server:
              serializePublicRoom(
                room
              ),

            version:
              GAME_VERSION
          }
        );
      }
    }

    room.lastHumanCount =
      count;

    return;
  }

  if (
    !room.soloSince
  ) {
    room.soloSince =
      now;
  }

  if (
    (
      force
      ||
      now
      -
      room.soloSince
      >=
      SOLO_NOTICE_DELAY_MS
    )
    &&
    !room.soloNoticeSent
  ) {
    room.waitingForPlayers =
      false;

    room.soloNoticeSent =
      true;

    const only =
      humans[0];

    if (only) {
      const socket =
        io.sockets.sockets.get(
          only.id
        );

      if (socket) {
        socket.emit(
          'publicSoloState',
          {
            server:
              serializePublicRoom(
                room
              ),

            version:
              GAME_VERSION,

            message:
              'Só tem você online neste servidor.'
          }
        );
      }
    }
  }

  room.lastHumanCount =
    count;
}

/* =========================================================
   PRIVATE LOBBY RETURN
========================================================= */

function finishPrivateRoundIfEmpty(
  room
) {
  if (
    !room
    ||
    room.type !==
    'private'
    ||
    !room.started
  ) {
    return false;
  }

  const humans =
    roomHumans(
      room
    );

  const anyoneStillInArena =
    humans.some(
      player =>
        player.alive
        &&
        player.inArena !== false
    );

  if (
    anyoneStillInArena
  ) {
    return false;
  }

  room.started =
    false;

  removeAllBots(
    room
  );

  room.foods.clear();

  for (
    const human
    of
    humans
  ) {
    human.alive =
      false;

    human.inArena =
      false;

    human.ready =
      false;

    human.boost =
      false;
  }

  emitLobby(
    room
  );

  return true;
}

/* =========================================================
   SOCKET.IO
========================================================= */

io.on(
  'connection',
  socket => {

    const player =
      createHuman(
        socket
      );

    players.set(
      socket.id,
      player
    );

    runtimeMetrics.joins++;

    console.log(
      `✅ conectado ${socket.id}`
    );

    socket.on(
      'clientPerformance',
      (
        data = {},
        ack
      ) => {

        const profile =
          applyClientPerformanceProfile(
            player,
            data
          );

        safeAck(
          ack,
          {
            ok: true,
            profile,
            version:
              GAME_VERSION
          }
        );
      }
    );

    socket.on(
      'joinPublicGame',
      (
        data = {},
        ack
      ) => {

        player.name =
          sanitizeName(
            data.name
          );

        player.skinId =
          sanitizeSkin(
            data.skinId
          );

        if (
          data.profileId
        ) {
          player.profileId =
            String(
              data.profileId
            )
            .slice(
              0,
              100
            );
        }

        let room =
          null;

        if (
          data.serverId
        ) {
          room =
            publicRooms.get(
              String(
                data.serverId
              )
              .toUpperCase()
            )
            ||
            null;
        }
        else {
          room =
            chooseAutoPublicServer();
        }

        if (!room) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Nenhum servidor público disponível.'
            }
          );
        }

        if (
          room.players.size >=
          MAX_ROOM_PLAYERS
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Servidor cheio.'
            }
          );
        }

        const payload =
          joinPublicRoom(
            socket,
            player,
            room
          );

        safeAck(
          ack,
          payload
        );
      }
    );

    socket.on(
      'findAlternativeServer',
      (
        _data,
        ack
      ) => {

        if (
          player.roomType !==
          'public'
          ||
          !player.roomId
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Você não está em um servidor público.'
            }
          );
        }

        const target =
          chooseAlternativePublicServer(
            player.roomId
          );

        if (
          !target
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Não encontramos outro servidor com jogadores online agora.'
            }
          );
        }

        safeAck(
          ack,
          {
            ok:
              true,

            target:
              serializePublicRoom(
                target
              ),

            version:
              GAME_VERSION
          }
        );
      }
    );

    socket.on(
      'switchPublicServer',
      (
        data = {},
        ack
      ) => {

        if (
          player.roomType !==
          'public'
          ||
          !player.roomId
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Você não está em um servidor público.'
            }
          );
        }

        const target =
          publicRooms.get(
            String(
              data.serverId
              ||
              ''
            )
            .toUpperCase()
          );

        if (
          !target
          ||
          target.code ===
          player.roomId
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Servidor de destino inválido.'
            }
          );
        }

        if (
          target.players.size >=
          MAX_ROOM_PLAYERS
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'O servidor de destino ficou cheio.'
            }
          );
        }

        const payload =
          joinPublicRoom(
            socket,
            player,
            target
          );

        safeAck(
          ack,
          payload
        );
      }
    );

    socket.on(
      'publicSoloAction',
      (
        data = {},
        ack
      ) => {

        if (
          player.roomType !==
          'public'
          ||
          !player.roomId
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Você não está em um servidor público.'
            }
          );
        }

        const room =
          publicRooms.get(
            player.roomId
          );

        if (!room) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Servidor não encontrado.'
            }
          );
        }

        const action =
          String(
            data.action
            ||
            ''
          );

        if (
          action ===
          'wait'
        ) {
          player.waitingSolo =
            true;

          player.inArena =
            false;

          player.alive =
            true;

          player.boost =
            false;

          room.waitingForPlayers =
            true;

          return safeAck(
            ack,
            {
              ok:
                true,

              waiting:
                true,

              server:
                serializePublicRoom(
                  room
                ),

              version:
                GAME_VERSION
            }
          );
        }

        if (
          action ===
          'leave'
        ) {
          detachPlayerFromRoom(
            player
          );

          return safeAck(
            ack,
            {
              ok:
                true,

              left:
                true,

              version:
                GAME_VERSION
            }
          );
        }

        return safeAck(
          ack,
          {
            ok:
              false,

            error:
              'Ação inválida.'
          }
        );
      }
    );

    socket.on(
      'resumePublicMatch',
      (
        _data,
        ack
      ) => {

        if (
          player.roomType !==
          'public'
          ||
          !player.roomId
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Você não está em um servidor público.'
            }
          );
        }

        const room =
          publicRooms.get(
            player.roomId
          );

        if (
          !room
          ||
          room.players.size <
          2
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Ainda não há outro jogador disponível.'
            }
          );
        }

        prepareSnake(
          player,
          room
        );

        player.pendingPublicResume =
          false;

        player.waitingSolo =
          false;

        room.waitingForPlayers =
          false;

        const payload = {
          ok:
            true,

          mode:
            'public',

          roomId:
            room.code,

          server:
            serializePublicRoom(
              room
            ),

          version:
            GAME_VERSION,

          player:
            serializePlayer(
              player,
              currentLeaderId(
                room
              )
            ),

          worldRadius:
            WORLD_RADIUS
        };

        emitFoods(
          room,
          socket
        );

        safeAck(
          ack,
          payload
        );
      }
    );

    socket.on(
      'createPrivateRoom',
      (
        data = {},
        ack
      ) => {

        detachPlayerFromRoom(
          player
        );

        player.name =
          sanitizeName(
            data.name
          );

        player.skinId =
          sanitizeSkin(
            data.skinId
          );

        const code =
          uniqueRoomCode();

        const botsEnabled =
          data.botsEnabled ===
          true;

        const botCount =
          botsEnabled
          ?
          clamp(
            Number(
              data.botCount
            )
            ||
            4,
            1,
            10
          )
          :
          0;

        const room =
          createRoom({
            code,

            name:
              sanitizeRoomName(
                data.roomName,
                player.name
              ),

            type:
              'private',

            hostId:
              player.id,

            botsEnabled,

            botCount,

            started:
              false,

            flag:
              '🔒'
          });

        privateRooms.set(
          code,
          room
        );

        room.players.add(
          player.id
        );

        player.roomId =
          code;

        player.roomType =
          'private';

        player.ready =
          false;

        player.alive =
          false;

        socket.join(
          code
        );

        const lobby =
          serializeLobby(
            room
          );

        const payload = {
          ok:
            true,

          code,

          lobby,

          version:
            GAME_VERSION
        };

        safeAck(
          ack,
          payload
        );

        socket.emit(
          'roomCreated',
          payload
        );

        emitLobby(
          room
        );
      }
    );

    socket.on(
      'joinPrivateRoom',
      (
        data = {},
        ack
      ) => {

        const code =
          String(
            data.code
            ||
            ''
          )
          .trim()
          .toUpperCase();

        const room =
          privateRooms.get(
            code
          );

        if (!room) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Sala não encontrada. Confira o código WILD-XXXX.'
            }
          );
        }

        if (
          room.players.size >=
          MAX_ROOM_PLAYERS
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Sala cheia.'
            }
          );
        }

        detachPlayerFromRoom(
          player
        );

        player.name =
          sanitizeName(
            data.name
          );

        player.skinId =
          sanitizeSkin(
            data.skinId
          );

        player.roomId =
          code;

        player.roomType =
          'private';

        player.ready =
          room.started;

        player.alive =
          false;

        room.players.add(
          player.id
        );

        socket.join(
          code
        );

        let arena =
          null;

        if (
          room.started
        ) {
          prepareSnake(
            player,
            room
          );

          ensureFood(
            room
          );

          arena = {
            ok:
              true,

            mode:
              'private',

            roomId:
              code,

            player:
              serializePlayer(
                player,
                currentLeaderId(
                  room
                )
              ),

            worldRadius:
              WORLD_RADIUS,

            version:
              GAME_VERSION
          };
        }

        const lobby =
          serializeLobby(
            room
          );

        const payload = {
          ok:
            true,

          code,

          started:
            room.started,

          lobby,

          arena,

          version:
            GAME_VERSION
        };

        safeAck(
          ack,
          payload
        );

        socket.emit(
          'roomJoined',
          payload
        );

        if (arena) {
          socket.emit(
            'onlineJoined',
            arena
          );

          emitFoods(
            room,
            socket
          );
        }

        emitLobby(
          room
        );
      }
    );

    socket.on(
      'toggleReady',
      (
        _data,
        ack
      ) => {

        const room =
          player.roomType ===
          'private'
          ?
          privateRooms.get(
            player.roomId
          )
          :
          null;

        if (!room) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Você não está em uma sala.'
            }
          );
        }

        if (
          room.started
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'A partida já começou.'
            }
          );
        }

        player.ready =
          !player.ready;

        const lobby =
          emitLobby(
            room
          );

        safeAck(
          ack,
          {
            ok:
              true,

            ready:
              player.ready,

            lobby
          }
        );
      }
    );

    socket.on(
      'startPrivateGame',
      (
        _data,
        ack
      ) => {

        const room =
          player.roomType ===
          'private'
          ?
          privateRooms.get(
            player.roomId
          )
          :
          null;

        if (!room) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Você não está em uma sala.'
            }
          );
        }

        if (
          room.hostId !==
          player.id
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Somente o dono da sala pode iniciar.'
            }
          );
        }

        const lobby =
          serializeLobby(
            room
          );

        if (
          !lobby.canStart
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                room.botsEnabled
                ?
                'Todos os jogadores devem marcar PRONTO.'
                :
                'São necessários pelo menos 2 jogadores e todos devem marcar PRONTO.'
            }
          );
        }

        room.started =
          true;

        room.foods.clear();

        ensureFood(
          room
        );

        removeAllBots(
          room
        );

        for (
          const id
          of
          room.players
        ) {
          const roomPlayer =
            players.get(
              id
            );

          if (
            !roomPlayer
          ) {
            continue;
          }

          roomPlayer.ready =
            true;

          prepareSnake(
            roomPlayer,
            room
          );

          const roomSocket =
            io.sockets.sockets.get(
              id
            );

          if (
            roomSocket
          ) {
            roomSocket.emit(
              'onlineJoined',
              {
                ok:
                  true,

                mode:
                  'private',

                roomId:
                  room.code,

                player:
                  serializePlayer(
                    roomPlayer,
                    currentLeaderId(
                      room
                    )
                  ),

                worldRadius:
                  WORLD_RADIUS,

                version:
                  GAME_VERSION
              }
            );

            emitFoods(
              room,
              roomSocket
            );
          }
        }

        if (
          room.botsEnabled
        ) {
          for (
            let i = 0;
            i < room.botCount;
            i++
          ) {
            createBot(
              room,
              i
            );
          }
        }

        io.to(
          room.code
        )
        .emit(
          'roomGameStarted',
          {
            ok:
              true,

            roomId:
              room.code,

            botsEnabled:
              room.botsEnabled,

            botCount:
              room.botCount,

            version:
              GAME_VERSION
          }
        );

        emitLobby(
          room
        );

        emitFoods(
          room
        );

        safeAck(
          ack,
          {
            ok:
              true,

            roomId:
              room.code,

            version:
              GAME_VERSION
          }
        );
      }
    );

    socket.on(
      'respawn',
      (
        _data,
        ack
      ) => {

        const room =
          player.roomId
          ?
          getRoom(
            player.roomId
          )
          :
          null;

        if (
          !room
          ||
          !room.started
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Não há partida ativa.'
            }
          );
        }

        if (
          room.type ===
          'public'
          &&
          room.players.size ===
          1
        ) {
          player.waitingSolo =
            true;

          player.alive =
            false;

          updatePublicSoloState(
            room,
            true
          );

          return safeAck(
            ack,
            {
              ok:
                false,

              waiting:
                true,

              error:
                'Você está sozinho nesta arena. Aguarde outro jogador ou procure outro servidor.'
            }
          );
        }

        prepareSnake(
          player,
          room
        );

        player.ready =
          true;

        const payload = {
          ok:
            true,

          mode:
            player.roomType,

          roomId:
            room.code,

          player:
            serializePlayer(
              player,
              currentLeaderId(
                room
              )
            ),

          worldRadius:
            WORLD_RADIUS,

          version:
            GAME_VERSION
        };

        emitFoods(
          room,
          socket
        );

        safeAck(
          ack,
          payload
        );

        if (
          room.type ===
          'private'
        ) {
          emitLobby(
            room
          );
        }
      }
    );

    socket.on(
      'input',
      (
        data = {}
      ) => {

        if (
          !player.roomId
          ||
          !player.alive
          ||
          player.waitingSolo
        ) {
          return;
        }

        const room =
          getRoom(
            player.roomId
          );

        if (
          !room
          ||
          !room.started
        ) {
          return;
        }

        if (
          Number.isFinite(
            data.angle
          )
        ) {
          player.targetAngle =
            norm(
              data.angle
            );
        }

        player.boost =
          data.boost ===
          true;

        player.lastInput =
          Date.now();
      }
    );

    socket.on(
      'clientPing',
      sentAt => {

        socket.emit(
          'serverPong',
          sentAt
        );
      }
    );

    socket.on(
      'returnPrivateLobby',
      (
        _data,
        ack
      ) => {

        if (
          player.roomType !==
          'private'
          ||
          !player.roomId
        ) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Você não está em uma sala privada.'
            }
          );
        }

        const room =
          privateRooms.get(
            player.roomId
          );

        if (!room) {
          return safeAck(
            ack,
            {
              ok:
                false,

              error:
                'Sala privada não encontrada.'
            }
          );
        }

        player.inArena =
          false;

        player.alive =
          false;

        player.boost =
          false;

        player.ready =
          false;

        finishPrivateRoundIfEmpty(
          room
        );

        const lobby =
          serializeLobby(
            room
          );

        emitLobby(
          room
        );

        safeAck(
          ack,
          {
            ok:
              true,

            lobby,

            roomId:
              room.code,

            version:
              GAME_VERSION
          }
        );
      }
    );

    socket.on(
      'leaveRoom',
      (
        _data,
        ack
      ) => {

        detachPlayerFromRoom(
          player
        );

        safeAck(
          ack,
          {
            ok:
              true,

            version:
              GAME_VERSION
          }
        );
      }
    );

    socket.on(
      'disconnect',
      reason => {

        runtimeMetrics.disconnects++;

        detachPlayerFromRoom(
          player
        );

        players.delete(
          player.id
        );

        console.log(
          `❌ saiu ${socket.id}: ${reason}`
        );
      }
    );
  }
);

/* =========================================================
   SERVER LOOPS
========================================================= */

const DT =
  1
  /
  TICK_RATE;

setInterval(
  () => {

    runtimeMetrics.physicsTicks++;

    for (
      const room
      of
      publicRooms.values()
    ) {
      if (
        room.players.size > 0
      ) {
        updateRoom(
          room,
          DT
        );
      }
    }

    for (
      const room
      of
      privateRooms.values()
    ) {
      if (
        room.started
      ) {
        updateRoom(
          room,
          DT
        );
      }
    }
  },

  1000
  /
  TICK_RATE
);

setInterval(
  () => {

    rebalanceAllPublicBots();

    for (
      const room
      of
      publicRooms.values()
    ) {
      updatePublicSoloState(
        room,
        false
      );
    }
  },

  500
);

setInterval(
  () => {

    for (
      const room
      of
      publicRooms.values()
    ) {
      if (
        room.players.size > 0
      ) {
        emitWorld(
          room
        );
      }
    }

    for (
      const room
      of
      privateRooms.values()
    ) {
      if (
        room.started
      ) {
        emitWorld(
          room
        );
      }
    }
  },

  1000
  /
  WORLD_BROADCAST_RATE
);

setInterval(
  () => {

    for (
      const room
      of
      publicRooms.values()
    ) {
      if (
        room.players.size > 0
      ) {
        emitFoods(
          room
        );
      }
    }

    for (
      const room
      of
      privateRooms.values()
    ) {
      if (
        room.started
      ) {
        emitFoods(
          room
        );
      }
    }
  },

  1000
  /
  FOOD_BROADCAST_RATE
);

/* =========================================================
   V13 - API DE CONTA LOCAL
========================================================= */

app.post(
  '/api/account/register',
  async(
    req,
    res
  ) => {

    const key =
      `register:${req.ip}`;

    if (
      !rateLimit(
        key,
        {
          windowMs:
            60_000,

          max:
            8
        }
      )
    ) {
      return res.status(
        429
      )
      .json({
        ok:
          false,

        error:
          'Muitas tentativas. Aguarde um minuto.'
      });
    }

    try {

      const result =
        await registerLocalAccount(
          req.body
          ||
          {}
        );

      res.status(
        result.ok
        ?
        200
        :
        400
      )
      .json(
        result
      );
    }
    catch (
      error
    ) {

      console.error(
        'register:',
        error
      );

      res.status(
        500
      )
      .json({
        ok:
          false,

        error:
          'Falha interna ao criar conta.'
      });
    }
  }
);

app.post(
  '/api/account/login',
  async(
    req,
    res
  ) => {

    const key =
      `login:${req.ip}`;

    if (
      !rateLimit(
        key,
        {
          windowMs:
            60_000,

          max:
            15
        }
      )
    ) {
      return res.status(
        429
      )
      .json({
        ok:
          false,

        error:
          'Muitas tentativas. Aguarde um minuto.'
      });
    }

    try {

      const result =
        await loginLocalAccount(
          req.body
          ||
          {}
        );

      res.status(
        result.ok
        ?
        200
        :
        401
      )
      .json(
        result
      );
    }
    catch (
      error
    ) {

      console.error(
        'login:',
        error
      );

      res.status(
        500
      )
      .json({
        ok:
          false,

        error:
          'Falha interna ao entrar.'
      });
    }
  }
);

app.get(
  '/api/account/me',
  (
    req,
    res
  ) => {

    const session =
      sessionFromRequest(
        req
      );

    if (
      !session
    ) {
      return res.status(
        401
      )
      .json({
        ok:
          false,

        error:
          'Sessão inválida ou expirada.'
      });
    }

    const account =
      persistentState.accounts[
        session.accountId
      ];

    if (
      !account
    ) {
      return res.status(
        404
      )
      .json({
        ok:
          false,

        error:
          'Conta não encontrada.'
      });
    }

    res.json({
      ok:
        true,

      account:
        publicAccountView(
          account
        )
    });
  }
);

app.post(
  '/api/account/profile',
  (
    req,
    res
  ) => {

    const session =
      sessionFromRequest(
        req
      );

    if (
      !session
    ) {
      return res.status(
        401
      )
      .json({
        ok:
          false,

        error:
          'Sessão inválida.'
      });
    }

    const account =
      persistentState.accounts[
        session.accountId
      ];

    if (
      !account
    ) {
      return res.status(
        404
      )
      .json({
        ok:
          false,

        error:
          'Conta não encontrada.'
      });
    }

    account.displayName =
      cleanDisplayName(
        req.body?.displayName
      )
      ||
      account.displayName;

    savePersistentState();

    res.json({
      ok:
        true,

      account:
        publicAccountView(
          account
        )
    });
  }
);

/* =========================================================
   V13 - API DE SKINS LIMITADAS
========================================================= */

app.get(
  '/api/shop/limited',
  (
    _req,
    res
  ) => {

    res.set(
      'Cache-Control',
      'no-store'
    );

    res.json({
      ok:
        true,

      version:
        GAME_VERSION,

      skins:
        limitedCatalogView()
    });
  }
);

app.post(
  '/api/shop/limited/purchase',
  (
    req,
    res
  ) => {

    const key =
      `limited:${req.ip}`;

    if (
      !rateLimit(
        key,
        {
          windowMs:
            10_000,

          max:
            12
        }
      )
    ) {
      return res.status(
        429
      )
      .json({
        ok:
          false,

        error:
          'Aguarde alguns segundos antes de tentar novamente.'
      });
    }

    const result =
      buyLimitedSkinForProfile(
        String(
          req.body?.skinId
          ||
          ''
        ),

        String(
          req.body?.profileId
          ||
          ''
        )
      );

    if (
      result.ok
    ) {
      runtimeMetrics.limitedPurchases++;
    }

    res.status(
      result.ok
      ?
      200
      :
      409
    )
    .json(
      result
    );
  }
);

/* =========================================================
   V13 - SMTP OPCIONAL PARA RELATÓRIOS
========================================================= */

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

function smtpConfigured() {
  return (
    SMTP_USER.includes(
      '@'
    )
    &&
    SMTP_APP_PASSWORD.length >= 8
  );
}

function smtpEncodeBase64(
  value
) {
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
) {
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
  timeoutMs = 8000
) {
  return new Promise(
    (
      resolve,
      reject
    ) => {

      let buffer =
        '';

      const timeout =
        setTimeout(
          () => {

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
        () => {

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
        error => {

          cleanup();

          reject(
            error
          );
        };

      const onData =
        chunk => {

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

          if (
            !lines.length
          ) {
            return;
          }

          const last =
            lines[
              lines.length - 1
            ];

          if (
            /^\d{3}\s/.test(
              last
            )
          ) {
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
) {
  if (
    command !== null
  ) {
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

  if (
    !expected.includes(
      response.code
    )
  ) {
    throw new Error(
      `SMTP ${response.code}: ${response.text.trim()}`
    );
  }

  return response;
}

async function sendBugReportEmail(
  report
) {
  if (
    !smtpConfigured()
  ) {
    return {
      ok:
        false,

      skipped:
        true,

      reason:
        'smtp-not-configured'
    };
  }

  const socket =
    tls.connect(
      {
        host:
          'smtp.gmail.com',

        port:
          465,

        servername:
          'smtp.gmail.com',

        rejectUnauthorized:
          true
      }
    );

  try {

    await new Promise(
      (
        resolve,
        reject
      ) => {

        const timer =
          setTimeout(
            () =>
              reject(
                new Error(
                  'SMTP connection timeout'
                )
              ),
            9000
          );

        socket.once(
          'secureConnect',
          () => {

            clearTimeout(
              timer
            );

            resolve();
          }
        );

        socket.once(
          'error',
          error => {

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

    if (
      accepted.code !==
      250
    ) {
      throw new Error(
        `SMTP ${accepted.code}`
      );
    }

    try {
      socket.write(
        'QUIT\r\n'
      );
    }
    catch {}

    return {
      ok:
        true,

      skipped:
        false
    };
  }
  catch (
    error
  ) {
    console.error(
      'Falha SMTP ao enviar bug:',
      error.message
    );

    return {
      ok:
        false,

      skipped:
        false,

      reason:
        error.message
    };
  }
  finally {
    try {
      socket.end();
    }
    catch {}
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
  ) => {

    const key =
      `bug:${req.ip}`;

    if (
      !rateLimit(
        key,
        {
          windowMs:
            60_000,

          max:
            6
        }
      )
    ) {
      return res.status(
        429
      )
      .json({
        ok:
          false,

        error:
          'Muitos relatórios em pouco tempo.'
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

    if (
      text.length < 5
    ) {
      return res.status(
        400
      )
      .json({
        ok:
          false,

        error:
          'Descreva o problema com um pouco mais de detalhes.'
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
          req.headers[
            'user-agent'
          ]
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

    if (
      persistentState.bugReports.length >
      500
    ) {
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
      ok:
        true,

      reportId:
        report.id,

      stored:
        true,

      emailConfigured:
        smtpConfigured(),

      emailSent:
        emailResult.ok === true,

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

      mailto:
        `mailto:${BUG_REPORT_EMAIL}?subject=${subject}&body=${body}`
    });
  }
);

/* =========================================================
   V13 - RUNTIME / DEBUG
========================================================= */

app.get(
  '/api/runtime',
  (
    _req,
    res
  ) => {

    res.set(
      'Cache-Control',
      'no-store'
    );

    res.json({
      ok:
        true,

      version:
        GAME_VERSION,

      build:
        BUILD,

      runtime:
        runtimeSnapshot()
    });
  }
);

/* =========================================================
   HTTP API
========================================================= */

app.get(
  '/api/health',
  (
    _req,
    res
  ) => {

    res.set(
      'Cache-Control',
      'no-store'
    );

    res.json({
      ok:
        true,

      game:
        'WildSnake',

      version:
        GAME_VERSION,

      build:
        BUILD,

      now:
        Date.now()
    });
  }
);

app.get(
  '/api/status',
  (
    _req,
    res
  ) => {

    res.set(
      'Cache-Control',
      'no-store'
    );

    res.json({
      online:
        true,

      game:
        'WildSnake',

      version:
        GAME_VERSION,

      build:
        BUILD,

      connectedHumans:
        [
          ...players.values()
        ]
        .filter(
          player =>
            !player.isBot
        )
        .length,

      publicServers:
        [
          ...publicRooms.values()
        ]
        .map(
          serializePublicRoom
        ),

      privateRooms:
        privateRooms.size,

      rooms:
        [
          ...privateRooms.values()
        ]
        .map(
          room => ({
            code:
              room.code,

            name:
              room.name,

            started:
              room.started,

            online:
              room.players.size,

            botsEnabled:
              room.botsEnabled,

            botCount:
              room.botCount
          })
        ),

      worldRadius:
        WORLD_RADIUS,

      tickRate:
        TICK_RATE,

      broadcastRate:
        WORLD_BROADCAST_RATE,

      foodBroadcastRate:
        FOOD_BROADCAST_RATE
    });
  }
);

/* =========================================================
   ROOT / GAME CLIENT
========================================================= */

app.get(
  '/',
  (
    req,
    res
  ) => {

    res.set(
      'Cache-Control',
      'no-store, no-cache, must-revalidate, proxy-revalidate'
    );

    res.sendFile(
      path.join(
        __dirname,
        'Public',
        'index.html'
      )
    );
  }
);

/* =========================================================
   STATIC / CACHE
========================================================= */

app.use(
  (
    req,
    res,
    next
  ) => {

    if (
      req.path === '/'
      ||
      req.path.endsWith(
        '.html'
      )
    ) {
      res.set(
        'Cache-Control',
        'no-store, no-cache, must-revalidate, proxy-revalidate'
      );
    }

    next();
  }
);

app.use(
  express.static(
    path.join(
      __dirname,
      'Public'
    )
  )
);

/* =========================================================
   SERVER ERRORS
========================================================= */

httpServer.on(
  'error',
  error => {

    console.error(
      '\n❌ ERRO AO INICIAR SERVIDOR:',
      error.message
    );

    if (
      error.code ===
      'EADDRINUSE'
    ) {
      console.error(
        `A porta ${PORT} já está ocupada. Feche o outro processo Node antes de iniciar.`
      );
    }
  }
);

process.on(
  'uncaughtException',
  error => {

    console.error(
      '❌ uncaughtException:',
      error
    );
  }
);

process.on(
  'unhandledRejection',
  error => {

    console.error(
      '❌ unhandledRejection:',
      error
    );
  }
);

/* =========================================================
   START
========================================================= */

httpServer.listen(
  PORT,
  '0.0.0.0',
  () => {

    console.log(
      '\n============================================================'
    );

    console.log(
      `🐍 WILDSNAKE ONLINE ${GAME_VERSION}`
    );

    console.log(
      `🔧 BUILD: ${BUILD}`
    );

    console.log(
      `🌐 http://localhost:${PORT}`
    );

    console.log(
      `❤️  http://localhost:${PORT}/api/health`
    );

    console.log(
      '✅ Rota / entrega Public/index.html explicitamente'
    );

    console.log(
      '✅ Multi-servidor: BR / US / EU / AS'
    );

    console.log(
      '✅ JOGAR AGORA escolhe automaticamente uma arena pública'
    );

    console.log(
      '✅ Lista manual de servidores via /api/status'
    );

    console.log(
      '✅ Comida online: pública + privada'
    );

    console.log(
      '✅ Comida de morte: ATIVA'
    );

    console.log(
      '✅ Bots adaptativos: ATIVOS quando há poucos humanos'
    );

    console.log(
      '✅ Bots com nomes naturais: ATIVO'
    );

    console.log(
      '✅ Colisão autoritativa contínua + anti-tunneling reforçado'
    );

    console.log(
      '✅ Corpo autoritativo enviado ao cliente'
    );

    console.log(
      '✅ Líder calculado no servidor (leaderId / isLeader)'
    );

    console.log(
      '✅ Modal solo + esperar + trocar servidor + sair'
    );

    console.log(
      '✅ Sala privada + lobby + pronto + bots + respawn'
    );

    console.log(
      `✅ Rede: ${WORLD_BROADCAST_RATE} world/s + ${FOOD_BROADCAST_RATE} food/s`
    );

    console.log(
      '============================================================\n'
    );
  }
);
