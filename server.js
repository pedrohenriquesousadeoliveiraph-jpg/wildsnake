const express = require('express');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const { Server } = require('socket.io');

const app = express();
const httpServer = http.createServer(app);

const io = new Server(httpServer, {
  cors: {
    origin: '*',
    methods: ['GET', 'POST']
  },

  transports: [
    'websocket',
    'polling'
  ],

  pingInterval: 10000,
  pingTimeout: 8000,
  connectTimeout: 12000,
  maxHttpBufferSize: 1e6
});


/* =========================================================
   WILDSNAKE SERVER CONFIG
========================================================= */

const PORT =
  Number(
    process.env.PORT || 3000
  );


const GAME_VERSION =
  'v12.36';


const BUILD =
  'wildsnake-v12.36-full-multiserver';


const WORLD_RADIUS =
  4200;


const SAFE_RADIUS =
  3900;


const BASE_SPEED =
  155;


const BOOST_MULT =
  1.85;


const MIN_LENGTH =
  16;


const SEGMENT_SPACING =
  13;


/*
    A física continua em 30 ticks.

    Isso deixa colisão e movimento
    independentes do FPS do navegador.
*/
const TICK_RATE =
  30;


/*
    Estado dos jogadores é enviado
    menos vezes que a física.

    Isso deixa o multiplayer mais leve.
*/
const WORLD_BROADCAST_RATE =
  12;


/*
    Comida muda menos que jogador.
*/
const FOOD_BROADCAST_RATE =
  2;


const FOOD_TARGET =
  180;


const FOOD_HARD_LIMIT =
  340;


const MAX_ROOM_PLAYERS =
  24;


/*
    Tempo antes de mostrar o modal
    quando há apenas um humano.
*/
const SOLO_NOTICE_DELAY_MS =
  2200;


/*
    Se o navegador parar de mandar input,
    não deixamos a cobra andando para
    sempre pelo mapa.
*/
const HUMAN_IDLE_FREEZE_MS =
  3000;


const HEAD_RADIUS =
  16;


const BODY_RADIUS =
  12;


const HEAD_HEAD_DISTANCE =
  HEAD_RADIUS * 2 - 1;


const HEAD_BODY_DISTANCE =
  HEAD_RADIUS + BODY_RADIUS + 2;



/* =========================================================
   ESTADO GLOBAL
========================================================= */

const players =
  new Map();


const privateRooms =
  new Map();


const publicRooms =
  new Map();



/* =========================================================
   SERVIDORES PÚBLICOS
========================================================= */

const PUBLIC_SERVER_DEFS = [

  {
    id:
      'BR-001',

    name:
      'Brasil #1',

    region:
      'BR',

    flag:
      '🇧🇷'
  },

  {
    id:
      'BR-002',

    name:
      'Brasil #2',

    region:
      'BR',

    flag:
      '🇧🇷'
  },

  {
    id:
      'BR-003',

    name:
      'Brasil #3',

    region:
      'BR',

    flag:
      '🇧🇷'
  },

  {
    id:
      'US-001',

    name:
      'US East #1',

    region:
      'US',

    flag:
      '🇺🇸'
  },

  {
    id:
      'US-002',

    name:
      'US West #1',

    region:
      'US',

    flag:
      '🇺🇸'
  },

  {
    id:
      'EU-001',

    name:
      'Europa #1',

    region:
      'EU',

    flag:
      '🇪🇺'
  },

  {
    id:
      'EU-002',

    name:
      'Europa #2',

    region:
      'EU',

    flag:
      '🇪🇺'
  },

  {
    id:
      'AS-001',

    name:
      'Ásia #1',

    region:
      'AS',

    flag:
      '🌏'
  }

];



/* =========================================================
   NOMES DOS BOTS
========================================================= */

const BOT_NAMES = [

  'Nox',
  'Kira',
  'Luna',
  'Rex',
  'Maya',
  'Neo',
  'Viper',
  'Sky',
  'Axel',
  'Iris',

  'Dash',
  'Milo',
  'Nova',
  'Jinx',
  'Echo',
  'Bolt',
  'Pixel',
  'Onyx',
  'Kai',
  'Zara',

  'Drake',
  'Mika',
  'Raven',
  'Zero',
  'Nyx',
  'Toby',
  'Flux',
  'Ace',
  'Orion',
  'Blaze',

  'Storm',
  'Astra',
  'Frost',
  'Jade',
  'Sonic',
  'Rogue',
  'Atlas',
  'Volt',
  'Comet',
  'Ghost'

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
  'disco'

];


const BOT_COLORS = [

  '#38a8ff',
  '#ff5574',
  '#a879ff',
  '#ffd447',
  '#ff8b38',
  '#22d3ee',
  '#e879f9',
  '#8cff55',
  '#35e69b',
  '#f472b6',
  '#fb7185',
  '#60a5fa'

];


const FOOD_COLORS = [

  '#35e69b',
  '#38a8ff',
  '#ff5574',
  '#a879ff',
  '#ffd447',
  '#ff8b38',
  '#22d3ee',
  '#e879f9'

];



/* =========================================================
   UTILIDADES
========================================================= */

function rand(
  min,
  max
){

  return (
    Math.random()
    *
    (
      max - min
    )
    +
    min
  );

}


function clamp(
  value,
  min,
  max
){

  return Math.max(
    min,
    Math.min(
      max,
      value
    )
  );

}


function norm(
  angle
){

  return Math.atan2(
    Math.sin(
      angle
    ),
    Math.cos(
      angle
    )
  );

}


function safeAck(
  ack,
  payload
){

  if(
    typeof ack !==
    'function'
  ){

    return;

  }


  try{

    ack(
      payload
    );

  }
  catch(
    error
  ){

    console.error(
      'ACK error:',
      error?.message || error
    );

  }

}


function uid(
  prefix = 'ID'
){

  return (
    `${prefix}-${crypto.randomBytes(6).toString('hex')}`
  );

}


function sanitizeName(
  value
){

  return (

    String(
      value ?? 'Player'
    )
    .replace(
      /[<>]/g,
      ''
    )
    .trim()
    .slice(
      0,
      18
    )

    ||

    'Player'

  );

}


function sanitizeSkin(
  value
){

  return (

    String(
      value ?? 'basic'
    )
    .replace(
      /[^a-zA-Z0-9_-]/g,
      ''
    )
    .slice(
      0,
      40
    )

    ||

    'basic'

  );

}


function sanitizeRoomName(
  value,
  owner
){

  return (

    String(
      value ?? ''
    )
    .replace(
      /[<>]/g,
      ''
    )
    .trim()
    .slice(
      0,
      28
    )

    ||

    `Sala de ${owner}`.slice(
      0,
      28
    )

  );

}



/* =========================================================
   CÓDIGO DE SALA PRIVADA
========================================================= */

function makeRoomCode(){

  const chars =
    'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';


  let tail =
    '';


  for(
    let i = 0;
    i < 4;
    i++
  ){

    tail +=
      chars[
        crypto.randomInt(
          0,
          chars.length
        )
      ];

  }


  return (
    `WILD-${tail}`
  );

}


function uniqueRoomCode(){

  let code;


  do{

    code =
      makeRoomCode();

  }
  while(
    privateRooms.has(
      code
    )
  );


  return code;

}



/* =========================================================
   MODELO DE ARENA
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

}){

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

    players:
      new Set(),

    botIds:
      new Set(),

    foods:
      new Map(),

    createdAt:
      Date.now(),

    active:
      type ===
      'private',

    waitingForPlayers:
      false,

    soloSince:
      0,

    lastHumanCount:
      0,

    leaderId:
      null

  };

}



/* =========================================================
   CRIAR TODAS AS ARENAS PÚBLICAS
========================================================= */

for(
  const def
  of
  PUBLIC_SERVER_DEFS
){

  publicRooms.set(

    def.id,

    createRoom({

      code:
        def.id,

      name:
        def.name,

      type:
        'public',

      started:
        true,

      botsEnabled:
        true,

      region:
        def.region,

      flag:
        def.flag

    })

  );

}



/* =========================================================
   CONSULTAS DE SALA
========================================================= */

function getRoom(
  code
){

  return (

    publicRooms.get(
      code
    )

    ||

    privateRooms.get(
      code
    )

    ||

    null

  );

}


function roomHumans(
  room
){

  return (

    [
      ...room.players
    ]
    .map(
      id =>
        players.get(
          id
        )
    )
    .filter(
      Boolean
    )

  );

}


function roomBots(
  room
){

  return (

    [
      ...room.botIds
    ]
    .map(
      id =>
        players.get(
          id
        )
    )
    .filter(
      Boolean
    )

  );

}


function roomSnakes(
  room
){

  return (

    [
      ...room.players,
      ...room.botIds
    ]
    .map(
      id =>
        players.get(
          id
        )
    )
    .filter(
      Boolean
    )

  );

}


function activeRoomSnakes(
  room
){

  return (
    roomSnakes(
      room
    )
    .filter(
      snake =>
        snake.alive
    )
  );

}



/* =========================================================
   COMIDA
========================================================= */

function randomPoint(){

  const angle =
    rand(
      0,
      Math.PI * 2
    );


  const radius =
    Math.sqrt(
      Math.random()
    )
    *
    (
      SAFE_RADIUS - 120
    );


  return {

    x:
      Math.cos(
        angle
      )
      *
      radius,

    y:
      Math.sin(
        angle
      )
      *
      radius

  };

}


function spawnFood(

  room,
  x = null,
  y = null,
  value = null,
  color = null

){

  if(
    room.foods.size >=
    FOOD_HARD_LIMIT
  ){

    return null;

  }


  const point =
    (
      x === null
      ||
      y === null
    )

    ?

    randomPoint()

    :

    {
      x,
      y
    };


  const food = {

    id:
      uid(
        'F'
      ),

    x:
      point.x,

    y:
      point.y,

    value:
      value
      ??
      Math.floor(
        rand(
          1,
          5
        )
      ),

    r:
      rand(
        4,
        7
      ),

    color:
      color
      ||
      FOOD_COLORS[
        Math.floor(
          rand(
            0,
            FOOD_COLORS.length
          )
        )
      ]

  };


  room.foods.set(
    food.id,
    food
  );


  return food;

}


function ensureFood(
  room
){

  if(
    !room
  ){

    return;

  }


  if(
    room.type ===
    'public'
    &&
    room.players.size ===
    0
  ){

    return;

  }


  while(
    room.foods.size <
    FOOD_TARGET
  ){

    spawnFood(
      room
    );

  }

}



/* =========================================================
   SPAWN SEGURO
========================================================= */

function findSpawn(
  room
){

  const alive =
    activeRoomSnakes(
      room
    );


  for(
    let tries = 0;
    tries < 120;
    tries++
  ){

    const angle =
      rand(
        0,
        Math.PI * 2
      );


    const radius =
      rand(
        500,
        SAFE_RADIUS - 500
      );


    const x =
      Math.cos(
        angle
      )
      *
      radius;


    const y =
      Math.sin(
        angle
      )
      *
      radius;


    if(
      alive.every(
        snake =>
          Math.hypot(

            x - snake.x,
            y - snake.y

          )
          >
          500
      )
    ){

      return {
        x,
        y
      };

    }

  }


  return {

    x:
      rand(
        -700,
        700
      ),

    y:
      rand(
        -700,
        700
      )

  };

}



/* =========================================================
   TRAIL / CORPO
========================================================= */

function seedTrail(
  snake
){

  snake.trail =
    [];


  for(
    let i = 0;
    i < 700;
    i++
  ){

    snake.trail.push({

      x:
        snake.x
        -
        Math.cos(
          snake.angle
        )
        *
        i
        *
        3,

      y:
        snake.y
        -
        Math.sin(
          snake.angle
        )
        *
        i
        *
        3

    });

  }


  snake.prevBodySegments =
    bodySegments(
      snake,
      0
    )
    .map(
      point => ({

        x:
          point.x,

        y:
          point.y

      })
    );

}


function updateTrail(
  snake
){

  snake.trail.unshift({

    x:
      snake.x,

    y:
      snake.y

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


  if(
    snake.trail.length >
    maxTrail
  ){

    snake.trail.length =
      maxTrail;

  }

}


function bodySegments(
  snake,
  offset = 0
){

  if(
    !Array.isArray(
      snake.trail
    )
    ||
    snake.trail.length ===
    0
  ){

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


  for(
    let i = 0;
    i < count;
    i++
  ){

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


    if(
      point
    ){

      result.push(
        point
      );

    }

  }


  return result;

}



/* =========================================================
   JOGADOR HUMANO
========================================================= */

function createHuman(
  socket
){

  return {

    id:
      socket.id,

    name:
      'Player',

    skinId:
      'basic',

    color:
      '#35e69b',

    roomId:
      null,

    roomType:
      null,

    ready:
      false,

    alive:
      false,

    isBot:
      false,

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
      BASE_SPEED,

    boost:
      false,

    length:
      18,

    score:
      0,

    kills:
      0,

    trail:
      [],

    prevBodySegments:
      [],

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

    connectedAt:
      Date.now()

  };

}



/* =========================================================
   PREPARAR COBRA
========================================================= */

function prepareSnake(
  snake,
  room
){

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


  seedTrail(
    snake
  );

}



/* =========================================================
   LÍDER
========================================================= */

function currentLeaderId(
  room
){

  const alive =
    activeRoomSnakes(
      room
    );


  if(
    alive.length ===
    0
  ){

    return null;

  }


  alive.sort(
    (
      a,
      b
    ) =>

      (
        b.score || 0
      )
      -
      (
        a.score || 0
      )

      ||

      (
        b.length || 0
      )
      -
      (
        a.length || 0
      )

      ||

      (
        b.kills || 0
      )
      -
      (
        a.kills || 0
      )

      ||

      String(
        a.id
      )
      .localeCompare(
        String(
          b.id
        )
      )

  );


  return (
    alive[0].id
  );

}



/* =========================================================
   SERIALIZAÇÃO
========================================================= */

function serializePlayer(
  snake,
  leaderId = null
){

  return {

    id:
      snake.id,

    name:
      snake.name,

    skinId:
      snake.skinId,

    color:
      snake.color,

    x:
      snake.x,

    y:
      snake.y,

    prevX:
      snake.prevX,

    prevY:
      snake.prevY,

    angle:
      snake.angle,

    boost:
      !!snake.boost,

    length:
      snake.length,

    score:
      snake.score,

    kills:
      snake.kills
      ||
      0,

    alive:
      !!snake.alive,

    isBot:
      !!snake.isBot,

    /*
        O cliente sabe quem é o líder.

        Assim o HTML pode desenhar a coroa
        na cabeça da cobra correta.
    */
    isLeader:
      snake.id ===
      leaderId,

    /*
        O corpo enviado é o MESMO corpo
        que o servidor utiliza nas colisões.

        Isso evita a diferença entre
        o que o usuário vê e o que
        realmente colide.
    */
    segments:
      bodySegments(
        snake,
        0
      )
      .slice(
        0,
        90
      )
      .map(
        point => ({

          x:
            point.x,

          y:
            point.y

        })
      )

  };

}


function serializePublicRoom(
  room
){

  return {

    id:
      room.code,

    name:
      room.name,

    region:
      room.region,

    flag:
      room.flag,

    humans:
      room.players.size,

    bots:
      room.botIds.size,

    total:
      room.players.size
      +
      room.botIds.size,

    active:
      room.players.size >
      0,

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
){

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


  for(
    let offset = 0;
    offset < BOT_NAMES.length;
    offset++
  ){

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


    if(
      !used.has(
        name
      )
    ){

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
){

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
      false

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
){

  room.botIds.delete(
    id
  );


  players.delete(
    id
  );

}


function removeAllBots(
  room
){

  for(
    const id
    of
    [
      ...room.botIds
    ]
  ){

    removeBot(
      room,
      id
    );

  }

}



/* =========================================================
   QUANTIDADE AUTOMÁTICA DE BOTS
========================================================= */

/*
    REGRA:

    Até 6 humanos:
    SEMPRE haverá bots.

    8 e 9 jogadores:
    continua com 4 bots,
    como havíamos combinado.

    Conforme aumenta a população,
    a IA diminui.
*/

function desiredPublicBots(
  humans
){

  if(
    humans <= 1
  ){

    return 10;

  }


  if(
    humans <= 2
  ){

    return 9;

  }


  if(
    humans <= 4
  ){

    return 7;

  }


  if(
    humans <= 6
  ){

    return 5;

  }


  if(
    humans <= 9
  ){

    return 4;

  }


  if(
    humans <= 12
  ){

    return 2;

  }


  return 0;

}


function rebalancePublicBots(
  room
){

  if(
    !room
    ||
    room.type !==
    'public'
  ){

    return;

  }


  const humans =
    room.players.size;


  /*
      Arena sem humanos é encerrada.

      O objeto do servidor continua
      existindo na lista BR/US/EU/AS,
      mas bots/comida são liberados.
  */
  if(
    humans ===
    0
  ){

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


  if(
    current <
    desired
  ){

    for(
      let i = current;
      i < desired;
      i++
    ){

      createBot(
        room,
        i
      );

    }

  }
  else if(
    current >
    desired
  ){

    const ids =
      [
        ...room.botIds
      ];


    for(
      let i = 0;
      i < current - desired;
      i++
    ){

      removeBot(
        room,
        ids[i]
      );

    }

  }

}


function rebalanceAllPublicBots(){

  for(
    const room
    of
    publicRooms.values()
  ){

    rebalancePublicBots(
      room
    );

  }

}



/* =========================================================
   LOBBY PRIVADO
========================================================= */

function serializeLobby(
  room
){

  const list =
    roomHumans(
      room
    )
    .map(
      player => ({

        id:
          player.id,

        name:
          player.name,

        skinId:
          player.skinId,

        ready:
          !!player.ready,

        host:
          room.hostId ===
          player.id,

        alive:
          !!player.alive,

        spectating:
          room.started
          &&
          !player.alive

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
    room.botCount >
    0

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
){

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
   REMOVER JOGADOR DA SALA
========================================================= */

function detachPlayerFromRoom(

  player,

  {
    emitLobbyState = true
  } = {}

){

  if(
    !player
    ||
    !player.roomId
  ){

    return null;

  }


  const room =
    getRoom(
      player.roomId
    );


  const oldRoomId =
    player.roomId;


  if(
    room
  ){

    room.players.delete(
      player.id
    );


    if(
      room.type ===
      'private'
    ){

      if(
        room.players.size ===
        0
      ){

        removeAllBots(
          room
        );


        room.foods.clear();


        privateRooms.delete(
          room.code
        );

      }
      else{

        /*
            Se o dono sair,
            transfere a liderança
            da sala para outro humano.
        */
        if(
          room.hostId ===
          player.id
        ){

          room.hostId =
            [
              ...room.players
            ][0];

        }


        if(
          emitLobbyState
        ){

          emitLobby(
            room
          );

        }

      }

    }
    else{

      /*
          Recalcula IA e o estado
          "sobrou só você".
      */
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


  if(
    socket
  ){

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


  return room;

}



/* =========================================================
   GEOMETRIA
========================================================= */

function pointSeg(

  px,
  py,

  ax,
  ay,

  bx,
  by

){

  const abx =
    bx - ax;


  const aby =
    by - ay;


  const den =
    abx * abx
    +
    aby * aby;


  if(
    den <
    1e-9
  ){

    return Math.hypot(
      px - ax,
      py - ay
    );

  }


  const t =
    clamp(

      (
        (
          px - ax
        )
        *
        abx

        +

        (
          py - ay
        )
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

){

  const value =
    (
      by - ay
    )
    *
    (
      cx - bx
    )
    -
    (
      bx - ax
    )
    *
    (
      cy - by
    );


  if(
    Math.abs(
      value
    )
    <
    1e-9
  ){

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

){

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

){

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


  if(
    o1 !== o2
    &&
    o3 !== o4
  ){

    return true;

  }


  if(
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
  ){

    return true;

  }


  if(
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
  ){

    return true;

  }


  if(
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
  ){

    return true;

  }


  if(
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
  ){

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

){

  if(
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
  ){

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



/* =========================================================
   CABEÇA X CABEÇA COM SWEEP
========================================================= */

function sweptHeads(
  a,
  b
){

  const r0x =
    a.prevX -
    b.prevX;


  const r0y =
    a.prevY -
    b.prevY;


  const drx =
    (
      a.x -
      a.prevX
    )
    -
    (
      b.x -
      b.prevX
    );


  const dry =
    (
      a.y -
      a.prevY
    )
    -
    (
      b.y -
      b.prevY
    );


  const den =
    drx * drx
    +
    dry * dry;


  const t =
    den >
    1e-9

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

    r0x
    +
    drx
    *
    t,

    r0y
    +
    dry
    *
    t

  );

}



/* =========================================================
   CABEÇA X CORPO CONTÍNUO
========================================================= */

function sweptHeadAgainstBody(

  attacker,
  defender

){

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


  if(
    current.length <
    4
  ){

    return Infinity;

  }


  let best =
    Infinity;


  /*
      Começa no segmento 2.

      Não deixamos uma abertura enorme
      na região logo atrás da cabeça.
  */
  for(
    let i = 2;
    i < current.length - 1;
    i++
  ){

    const c1 =
      current[i];


    const c2 =
      current[
        i + 1
      ];


    if(
      !c1
      ||
      !c2
    ){

      continue;

    }


    /*
        Caminho da cabeça contra
        corpo atual.
    */
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


    if(
      p1
      &&
      p2
    ){

      /*
          Contra posição anterior
          do corpo.
      */
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


      /*
          Sweep lateral do primeiro
          ponto da cápsula.
      */
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


      /*
          Sweep lateral do segundo
          ponto da cápsula.
      */
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


    if(
      best <=
      HEAD_BODY_DISTANCE
    ){

      return best;

    }

  }


  return best;

}



/* =========================================================
   COMIDA DE MORTE
========================================================= */

function scatterDeathFood(
  room,
  snake
){

  const body =
    bodySegments(
      snake,
      0
    );


  for(
    let i = 1;
    i < body.length;
    i += 2
  ){

    if(
      room.foods.size >=
      FOOD_HARD_LIMIT
    ){

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

            (
              snake.score || 1
            )
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



/* =========================================================
   MORTE
========================================================= */

function killSnake(

  room,
  snake,
  reason,
  killer = null

){

  if(
    !snake
    ||
    !snake.alive
  ){

    return;

  }


  snake.alive =
    false;


  snake.boost =
    false;


  scatterDeathFood(
    room,
    snake
  );


  if(
    killer
    &&
    killer !== snake
    &&
    killer.alive
  ){

    killer.kills =
      (
        killer.kills
        ||
        0
      )
      +
      1;


    killer.score =
      (
        killer.score
        ||
        0
      )
      +
      25;

  }


  if(
    snake.isBot
  ){

    snake.respawnAt =
      Date.now()
      +
      rand(
        1800,
        3200
      );


    return;

  }


  const socket =
    io.sockets.sockets.get(
      snake.id
    );


  if(
    socket
  ){

    socket.emit(
      'playerDied',
      {

        reason,

        score:
          Math.floor(
            snake.score
            ||
            0
          ),

        kills:
          snake.kills
          ||
          0,

        length:
          Number(
            (
              snake.length
              ||
              18
            )
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


  if(
    room.type ===
    'private'
  ){

    emitLobby(
      room
    );

  }

}



/* =========================================================
   MOVIMENTO
========================================================= */

function moveSnake(

  snake,
  dt,
  turnSpeed = 3.2

){

  /*
      Guarda o corpo anterior ANTES
      de mover.

      Isso fortalece a colisão
      contra atravessamento.
  */
  snake.prevBodySegments =
    bodySegments(
      snake,
      0
    )
    .map(
      point => ({

        x:
          point.x,

        y:
          point.y

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


  if(
    snake.boost
    &&
    snake.length >
    MIN_LENGTH
  ){

    speed *=
      BOOST_MULT;


    snake.length =
      Math.max(

        MIN_LENGTH,

        snake.length
        -
        0.32
        *
        dt

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
   IA DOS BOTS
========================================================= */

function nearestFood(

  room,
  bot,
  maxDistance = 850

){

  let best =
    null;


  let bestDistance =
    maxDistance;


  for(
    const food
    of
    room.foods.values()
  ){

    const distance =
      Math.hypot(

        food.x -
        bot.x,

        food.y -
        bot.y

      );


    if(
      distance <
      bestDistance
    ){

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

){

  let best =
    null;


  let bestDistance =
    maxDistance;


  for(
    const human
    of
    roomHumans(
      room
    )
  ){

    if(
      !human.alive
      ||
      human.waitingSolo
    ){

      continue;

    }


    const distance =
      Math.hypot(

        human.x -
        bot.x,

        human.y -
        bot.y

      );


    if(
      distance <
      bestDistance
    ){

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

){

  if(
    !bot.alive
  ){

    if(
      bot.respawnAt
      &&
      Date.now() >=
      bot.respawnAt
    ){

      prepareSnake(
        bot,
        room
      );

    }


    return;

  }


  bot.aiTimer -=
    dt;


  if(
    bot.aiTimer <=
    0
  ){

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


    /*
        Volta para dentro do mapa.
    */
    if(
      center >
      SAFE_RADIUS - 520
    ){

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

    /*
        Bot comete erros.
    */
    else if(
      Math.random() <
      bot.mistake
    ){

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

    /*
        Às vezes tenta ir atrás
        de humano.
    */
    else if(
      human
      &&
      Math.random() <
      bot.aggression
    ){

      bot.targetAngle =
        Math.atan2(

          human.y -
          bot.y,

          human.x -
          bot.x

        )
        +
        rand(
          -0.26,
          0.26
        );

    }

    /*
        Prioriza comida.
    */
    else if(
      food
    ){

      bot.targetAngle =
        Math.atan2(

          food.y -
          bot.y,

          food.x -
          bot.x

        )
        +
        rand(
          -0.22,
          0.22
        );

    }

    else{

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
      bot.length >
      20
      &&
      Math.random() <
      0.06;

  }


  moveSnake(
    bot,
    dt,
    2.15
  );

}



/* =========================================================
   COMER
========================================================= */

function eatFood(
  room,
  snake
){

  let eaten =
    0;


  for(
    const [
      id,
      food
    ]
    of
    room.foods
  ){

    if(
      Math.hypot(

        snake.x -
        food.x,

        snake.y -
        food.y

      )
      <
      HEAD_RADIUS
      +
      food.r
      +
      4
    ){

      room.foods.delete(
        id
      );


      snake.score +=
        food.value;


      snake.length +=
        food.value
        *
        0.11;


      eaten++;


      /*
          Impede loop pesado se várias
          comidas estiverem exatamente
          na mesma posição.
      */
      if(
        eaten >=
        3
      ){

        break;

      }

    }

  }

}



/* =========================================================
   COLISÕES
========================================================= */

function handleCollisions(
  room
){

  let alive =
    activeRoomSnakes(
      room
    );


  /* =====================================================
     BORDA
  ===================================================== */

  for(
    const snake
    of
    alive
  ){

    if(
      Math.hypot(
        snake.x,
        snake.y
      )
      >
      SAFE_RADIUS
    ){

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
    );


  /* =====================================================
     CABEÇA X CABEÇA

     OS DOIS MORREM.
  ===================================================== */

  for(
    let i = 0;
    i < alive.length;
    i++
  ){

    const a =
      alive[i];


    if(
      !a.alive
    ){

      continue;

    }


    for(
      let j = i + 1;
      j < alive.length;
      j++
    ){

      const b =
        alive[j];


      if(
        !b.alive
      ){

        continue;

      }


      const currentDistance =
        Math.hypot(

          a.x -
          b.x,

          a.y -
          b.y

        );


      const sweptDistance =
        sweptHeads(
          a,
          b
        );


      if(
        currentDistance <=
        HEAD_HEAD_DISTANCE

        ||

        sweptDistance <=
        HEAD_HEAD_DISTANCE
      ){

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
    );


  /* =====================================================
     CABEÇA X CORPO

     SÓ QUEM BATE MORRE.
  ===================================================== */

  for(
    const attacker
    of
    alive
  ){

    if(
      !attacker.alive
    ){

      continue;

    }


    for(
      const defender
      of
      alive
    ){

      if(
        attacker ===
        defender
        ||
        !attacker.alive
        ||
        !defender.alive
      ){

        continue;

      }


      const distance =
        sweptHeadAgainstBody(
          attacker,
          defender
        );


      if(
        distance <=
        HEAD_BODY_DISTANCE
      ){

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
   ATUALIZAÇÃO DA ARENA
========================================================= */

function updateRoom(
  room,
  dt
){

  if(
    !room.started
  ){

    return;

  }


  for(
    const snake
    of
    roomSnakes(
      room
    )
  ){

    /*
        BOT
    */
    if(
      snake.isBot
    ){

      updateBot(
        room,
        snake,
        dt
      );

    }

    /*
        HUMANO
    */
    else if(
      snake.alive
      &&
      !snake.waitingSolo
    ){

      /*
          Se ficou sem mandar input,
          congela.

          Isso é importante quando
          alguém volta para o lobby
          da sala privada.
      */
      if(
        Date.now()
        -
        snake.lastInput
        <=
        HUMAN_IDLE_FREEZE_MS
      ){

        moveSnake(
          snake,
          dt,
          3.2
        );

      }
      else{

        snake.boost =
          false;


        snake.prevX =
          snake.x;


        snake.prevY =
          snake.y;

      }

    }


    if(
      snake.alive
      &&
      !snake.waitingSolo
    ){

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
   WORLD STATE
========================================================= */

function emitWorld(
  room
){

  room.leaderId =
    currentLeaderId(
      room
    );


  const leaderId =
    room.leaderId;


  io.to(
    room.code
  )
  .emit(
    'worldState',
    {

      roomId:
        room.code,

      serverTime:
        Date.now(),

      version:
        GAME_VERSION,

      /*
          Cliente pode usar isso
          para desenhar a coroa.
      */
      leaderId,

      server:
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

        },

      players:
        activeRoomSnakes(
          room
        )
        .map(
          snake =>
            serializePlayer(
              snake,
              leaderId
            )
        )

    }
  );

}



/* =========================================================
   FOOD STATE
========================================================= */

function emitFoods(

  room,
  socket = null

){

  const payload = {

    roomId:
      room.code,

    version:
      GAME_VERSION,

    foods:
      [
        ...room.foods.values()
      ]

  };


  if(
    socket
  ){

    socket.emit(
      'foodState',
      payload
    );

  }
  else{

    io.to(
      room.code
    )
    .emit(
      'foodState',
      payload
    );

  }

}



/* =========================================================
   ESCOLHER SERVIDOR AUTOMATICAMENTE
========================================================= */

function chooseAutoPublicServer(
  excludeId = null
){

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


  /*
      Primeiro prioriza servidor
      que já possui pessoas.
  */
  const occupied =
    all.filter(
      room =>
        room.players.size >
        0
    );


  const pool =
    occupied.length
    ?
    occupied
    :
    all;


  /*
      Entre os servidores ocupados,
      escolhe o menos cheio.
  */
  pool.sort(
    (
      a,
      b
    ) =>

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



/* =========================================================
   PROCURAR OUTRO SERVIDOR
========================================================= */

function chooseAlternativePublicServer(
  currentId
){

  const rooms =
    [
      ...publicRooms.values()
    ]
    .filter(
      room =>

        room.code !==
        currentId

        &&

        room.players.size >
        0

        &&

        room.players.size <
        MAX_ROOM_PLAYERS

    );


  rooms.sort(
    (
      a,
      b
    ) =>

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
   ENTRAR EM SERVIDOR PÚBLICO
========================================================= */

function joinPublicRoom(

  socket,
  player,
  room

){

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


  /*
      Comida já é criada
      no momento que entra.
  */
  ensureFood(
    room
  );


  /*
      Bots já aparecem
      no primeiro jogador.
  */
  rebalancePublicBots(
    room
  );


  /*
      Atualiza lógica de solo.
  */
  updatePublicSoloState(
    room,
    false
  );


  const leaderId =
    currentLeaderId(
      room
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
        leaderId
      ),

    worldRadius:
      WORLD_RADIUS

  };


  /*
      Não espera 2 segundos
      para mandar comida.
  */
  emitFoods(
    room,
    socket
  );


  return payload;

}



/* =========================================================
   ESTADO SOLO
========================================================= */

function updatePublicSoloState(

  room,
  force = false

){

  if(
    !room
    ||
    room.type !==
    'public'
  ){

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


  /*
      NINGUÉM
  */
  if(
    count ===
    0
  ){

    room.waitingForPlayers =
      false;


    room.soloSince =
      0;


    room.lastHumanCount =
      0;


    return;

  }


  /*
      2 OU MAIS HUMANOS
  */
  if(
    count >=
    2
  ){

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


    for(
      const player
      of
      waiting
    ){

      player.pendingPublicResume =
        true;


      const socket =
        io.sockets.sockets.get(
          player.id
        );


      if(
        socket
      ){

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


  /*
      APENAS 1 HUMANO.

      Agora isso funciona mesmo se
      a pessoa entrou sozinha desde
      o começo.

      O atraso evita o modal aparecer
      por cima do loading inicial.
  */
  if(
    !room.soloSince
  ){

    room.soloSince =
      now;

  }


  if(
    force

    ||

    now -
    room.soloSince
    >=
    SOLO_NOTICE_DELAY_MS
  ){

    room.waitingForPlayers =
      true;


    const only =
      humans[0];


    if(
      only
      &&
      !only.waitingSolo
    ){

      only.waitingSolo =
        true;


      only.boost =
        false;


      only.alive =
        false;


      const socket =
        io.sockets.sockets.get(
          only.id
        );


      if(
        socket
      ){

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


    console.log(
      `✅ conectado ${socket.id}`
    );



    /* =====================================================
       JOGAR AGORA / SERVIDOR MANUAL
    ===================================================== */

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


        let room =
          null;


        /*
            Se veio da tela SERVIDORES,
            usa o servidor escolhido.
        */
        if(
          data.serverId
        ){

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

        /*
            JOGAR AGORA:
            escolhe automaticamente.
        */
        else{

          room =
            chooseAutoPublicServer();

        }


        if(
          !room
        ){

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


        if(
          room.players.size >=
          MAX_ROOM_PLAYERS
        ){

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



    /* =====================================================
       PROCURAR OUTRO SERVIDOR
    ===================================================== */

    socket.on(
      'findAlternativeServer',
      (
        _data,
        ack
      ) => {


        if(
          player.roomType !==
          'public'
          ||
          !player.roomId
        ){

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


        if(
          !target
        ){

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



    /* =====================================================
       TROCAR DE SERVIDOR
    ===================================================== */

    socket.on(
      'switchPublicServer',
      (
        data = {},
        ack
      ) => {


        if(
          player.roomType !==
          'public'
          ||
          !player.roomId
        ){

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


        if(
          !target
          ||
          target.code ===
          player.roomId
        ){

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


        if(
          target.players.size >=
          MAX_ROOM_PLAYERS
        ){

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



    /* =====================================================
       AÇÃO DO MODAL SOLO
    ===================================================== */

    socket.on(
      'publicSoloAction',
      (
        data = {},
        ack
      ) => {


        if(
          player.roomType !==
          'public'
          ||
          !player.roomId
        ){

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


        if(
          !room
        ){

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


        /*
            ESPERAR
        */
        if(
          action ===
          'wait'
        ){

          player.waitingSolo =
            true;


          player.alive =
            false;


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


        /*
            SAIR
        */
        if(
          action ===
          'leave'
        ){

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


        safeAck(
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



    /* =====================================================
       VOLTAR À PARTIDA DEPOIS DE ESPERAR
    ===================================================== */

    socket.on(
      'resumePublicMatch',
      (
        _data,
        ack
      ) => {


        if(
          player.roomType !==
          'public'
          ||
          !player.roomId
        ){

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


        if(
          !room
          ||
          room.players.size <
          2
        ){

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


        const leaderId =
          currentLeaderId(
            room
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
              leaderId
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



    /* =====================================================
       CRIAR SALA PRIVADA
    ===================================================== */

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



    /* =====================================================
       ENTRAR EM SALA PRIVADA
    ===================================================== */

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


        if(
          !room
        ){

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


        if(
          room.players.size >=
          MAX_ROOM_PLAYERS
        ){

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


        /*
            Entrou em sala que
            já está jogando:

            entra na partida.
        */
        if(
          room.started
        ){

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


        if(
          arena
        ){

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



    /* =====================================================
       PRONTO
    ===================================================== */

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


        if(
          !room
        ){

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


        if(
          room.started
        ){

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



    /* =====================================================
       INICIAR SALA PRIVADA
    ===================================================== */

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


        if(
          !room
        ){

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


        if(
          room.hostId !==
          player.id
        ){

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


        if(
          !lobby.canStart
        ){

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


        /*
            Cada nova partida privada
            começa com comida nova.
        */
        room.foods.clear();


        ensureFood(
          room
        );


        /*
            Remove bots antigos antes
            de montar a nova partida.
        */
        removeAllBots(
          room
        );


        /*
            Prepara todos os humanos.
        */
        for(
          const id
          of
          room.players
        ){

          const roomPlayer =
            players.get(
              id
            );


          if(
            !roomPlayer
          ){

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


          if(
            roomSocket
          ){

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


            /*
                Comida imediatamente
                para cada cliente.
            */
            emitFoods(
              room,
              roomSocket
            );

          }

        }


        /*
            Bots opcionais da sala.
        */
        if(
          room.botsEnabled
        ){

          for(
            let i = 0;
            i < room.botCount;
            i++
          ){

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



    /* =====================================================
       RESPAWN
    ===================================================== */

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


        if(
          !room
          ||
          !room.started
        ){

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


        /*
            Em servidor público sozinho,
            não deixa simplesmente
            renascer escondendo o modal.
        */
        if(
          room.type ===
          'public'
          &&
          room.players.size ===
          1
        ){

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


        if(
          room.type ===
          'private'
        ){

          emitLobby(
            room
          );

        }

      }
    );



    /* =====================================================
       INPUT
    ===================================================== */

    socket.on(
      'input',
      (
        data = {}
      ) => {


        if(
          !player.roomId
          ||
          !player.alive
          ||
          player.waitingSolo
        ){

          return;

        }


        const room =
          getRoom(
            player.roomId
          );


        if(
          !room
          ||
          !room.started
        ){

          return;

        }


        if(
          Number.isFinite(
            data.angle
          )
        ){

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



    /* =====================================================
       PING
    ===================================================== */

    socket.on(
      'clientPing',
      sentAt => {


        socket.emit(
          'serverPong',
          sentAt
        );

      }
    );



    /* =====================================================
       SAIR DA SALA
    ===================================================== */

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



    /* =====================================================
       DISCONNECT
    ===================================================== */

    socket.on(
      'disconnect',
      reason => {


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
   LOOP PRINCIPAL DA FÍSICA
========================================================= */

const DT =
  1
  /
  TICK_RATE;


setInterval(
  () => {


    /*
        SERVIDORES PÚBLICOS
    */
    for(
      const room
      of
      publicRooms.values()
    ){

      if(
        room.players.size >
        0
      ){

        updateRoom(
          room,
          DT
        );

      }

    }


    /*
        SALAS PRIVADAS
    */
    for(
      const room
      of
      privateRooms.values()
    ){

      if(
        room.started
      ){

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



/* =========================================================
   CONTROLE DE BOTS + ESTADO SOLO
========================================================= */

setInterval(
  () => {


    rebalanceAllPublicBots();


    for(
      const room
      of
      publicRooms.values()
    ){

      updatePublicSoloState(
        room,
        false
      );

    }

  },

  500

);



/* =========================================================
   BROADCAST DE JOGADORES
========================================================= */

setInterval(
  () => {


    /*
        SERVIDORES PÚBLICOS
    */
    for(
      const room
      of
      publicRooms.values()
    ){

      if(
        room.players.size >
        0
      ){

        emitWorld(
          room
        );

      }

    }


    /*
        SALAS PRIVADAS
    */
    for(
      const room
      of
      privateRooms.values()
    ){

      if(
        room.started
      ){

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



/* =========================================================
   BROADCAST DE COMIDA
========================================================= */

setInterval(
  () => {


    for(
      const room
      of
      publicRooms.values()
    ){

      if(
        room.players.size >
        0
      ){

        emitFoods(
          room
        );

      }

    }


    for(
      const room
      of
      privateRooms.values()
    ){

      if(
        room.started
      ){

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
   HEALTH
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



/* =========================================================
   STATUS COMPLETO
========================================================= */

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

      /*
          É esta lista que a página
          SERVIDORES deve usar.
      */
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
   CACHE
========================================================= */

app.use(
  (
    req,
    res,
    next
  ) => {


    if(
      req.path ===
      '/'
      ||
      req.path.endsWith(
        '.html'
      )
    ){

      res.set(
        'Cache-Control',
        'no-store, no-cache, must-revalidate, proxy-revalidate'
      );

    }


    next();

  }
);



/* =========================================================
   PUBLIC
========================================================= */

app.use(
  express.static(
    path.join(
      __dirname,
      'Public'
    )
  )
);



/* =========================================================
   ERROS DO SERVIDOR
========================================================= */

httpServer.on(
  'error',
  error => {


    console.error(
      '\n❌ ERRO AO INICIAR SERVIDOR:',
      error.message
    );


    if(
      error.code ===
      'EADDRINUSE'
    ){

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