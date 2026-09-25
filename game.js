
"use strict";

const RESOURCES = ["wood", "brick", "wool", "grain", "ore"];
const TRADE_REQUEST_MAX = 19;
const RESOURCE_JA = { wood:"木材", brick:"レンガ", wool:"羊毛", grain:"小麦", ore:"鉱石" };
const RESOURCE_ICON = { wood:"🌲", brick:"🧱", wool:"🐑", grain:"🌾", ore:"🪨" };
const PLAYER_COLORS = ["#e53935", "#1976d2", "#f9a825", "#7b1fa2", "#00897b", "#6d4c41"];
const COST = {
  road: {wood:1, brick:1},
  settlement: {wood:1, brick:1, wool:1, grain:1},
  city: {grain:2, ore:3},
  dev: {wool:1, grain:1, ore:1},
};
const PIPS = {2:1,3:2,4:3,5:4,6:5,8:5,9:4,10:3,11:2,12:1};
const TILE_IMAGE_PATH = "assets/tiles";
const FISH_ACTION_COST = {removeRobber:2,steal:3,resource:4,road:5,dev:7};

// v1.50: CPUの「見える行動」同士は2秒空ける。
// AI内部の評価計算には待機を入れず、盤面を変える処理だけを間引く。
const CPU_ACTION_DELAY_MS = 2000;

const svg = document.getElementById("board");
const NS = "http://www.w3.org/2000/svg";
const $ = (id) => document.getElementById(id);

let game = null;
let cpuTimer = null;
let cpuActionRunning = false;
let cpuScheduledKey = null;

let cpuDiscardTimer = null;
let cpuDiscardScheduledKey = null;
const cpuStrategicGoalCache = new Map();
const cpuRoadSequenceCache = new Map();

let discardQueue = [];
let discardSelection = null;
let choiceModalState = null;
let tradeDraft = null;
let shownPendingTradeId = null;
const locallyResolvedTradeIds = new Set();
const shownAwardEventIds = new Set();
const shownResourcePopEventIds = new Set();
const shownTurnAnnouncementEventIds = new Set();
const awardDisplayQueue = [];
let turnAnnouncementTimer = null;
let awardDisplayActive = false;
let awardDisplayTimer = null;
let finalResultAutoTimer = null;
let finalResultWinnerKey = null;
let shownFishSwapKey = null;
let pendingPlacementPreview = null;
let boardPingMode = false;
let boardPingEvents = [];

const DESKTOP_1080_FIT_STORAGE_KEY=
  "catan-desktop-1080-fit";

let desktop1080FitEnabled=
  localStorage.getItem(
    DESKTOP_1080_FIT_STORAGE_KEY
  )==="1";

let boardRenderGeneration = 0;
const preloadedTileImages = [];

function rand(n){ return Math.floor(Math.random()*n); }
function shuffle(arr){
  const a=[...arr];
  for(let i=a.length-1;i>0;i--){ const j=rand(i+1); [a[i],a[j]]=[a[j],a[i]]; }
  return a;
}
function keyPoint(x,y){ return `${Math.round(x*10)/10},${Math.round(y*10)/10}`; }
function edgeKey(a,b){ return a < b ? `${a}|${b}` : `${b}|${a}`; }
function deepClone(x){ return JSON.parse(JSON.stringify(x)); }

// v1.53: CPU解析データ。
// 詳細ログはホストPCのIndexedDBへ保存する。
// 人間行動は「正式受理確認用の小さなレシート」だけ通常stateへ載せ、
// Workerから返った後にホストが解析ログへ確定する。
// 終了時だけ軽量化した1試合分を解析保存APIへ1回送信する。
const CPU_ANALYSIS_SCHEMA_VERSION=2;
const CPU_ANALYSIS_DB_NAME="catan-cpu-analysis";
const CPU_ANALYSIS_DB_VERSION=1;
const CPU_ANALYSIS_STORE="matches";
const CPU_ANALYSIS_MAX_MATCHES=12;
const CPU_ANALYSIS_MAX_EVENTS=12000;
const CPU_ANALYSIS_APP_VERSION="v1.55";
const CPU_ANALYSIS_LOGIC_VERSION="MAX_BEAM_V155_ROAD_BALANCE";
const CPU_ANALYSIS_SERVER_COMPACT_VERSION=1;

let cpuAnalysisSession=null;
let cpuAnalysisEventSeq=0;
let cpuAnalysisPersistTimer=null;
let cpuAnalysisEventsSincePersist=0;
let cpuAnalysisLastPersistAt=0;
const cpuAnalysisDedupeKeys=new Set();

function cpuAnalysisNowIso(){
  return new Date().toISOString();
}

function cpuAnalysisRound(value,digits=3){
  if(!Number.isFinite(value)) return null;
  const factor=10**digits;
  return Math.round(value*factor)/factor;
}

function cpuAnalysisClone(value){
  if(value===undefined) return null;
  try{
    return JSON.parse(JSON.stringify(value));
  }catch(_error){
    return null;
  }
}

function cpuAnalysisBoardSignature(){
  if(!game?.board) return "none";
  return game.board.hexes.map(hex=>[
    hex.id,
    hex.resource,
    hex.number??"",
    (hex.lakeNumbers||[]).join("."),
  ].join(":" )).join("|");
}

function cpuAnalysisBoardSnapshot(){
  if(!game?.board) return null;
  return {
    large:!!game.board.large,
    numberStart:game.board.numberStart??null,
    hexes:game.board.hexes.map(hex=>({
      id:hex.id,
      q:hex.q,
      r:hex.r,
      resource:hex.resource,
      number:hex.number??null,
      lakeNumbers:hex.lakeNumbers?[...hex.lakeNumbers]:null,
      corners:[...hex.corners],
    })),
    vertices:Object.values(game.board.vertices).map(vertex=>({
      id:vertex.id,
      hexes:[...vertex.hexes],
      edges:[...vertex.edges],
    })),
    edges:Object.values(game.board.edges).map(edge=>({
      id:edge.id,
      a:edge.a,
      b:edge.b,
      hexes:[...edge.hexes],
      harbor:edge.harbor??null,
    })),
    fishingGrounds:(game.board.fishingGrounds||[]).map(ground=>({
      id:ground.id,
      vertexId:ground.vertexId,
      number:ground.number,
    })),
  };
}

function cpuAnalysisResourceRates(player){
  if(!player || !game) return null;
  return Object.fromEntries(
    RESOURCES.map(resource=>[
      resource,
      cpuAnalysisRound(cpuResourceExpectedPerTurn(player,resource),4),
    ])
  );
}

function cpuAnalysisPlayerSnapshot(player,detailed=true){
  if(!player || !game) return null;
  const base={
    id:player.id,
    name:player.name,
    human:!!player.human,
    publicVP:publicVP(player),
    totalVP:totalVP(player),
    victoryTarget:victoryTarget(player),
    resources:{...player.resources},
    resourceTotal:totalResources(player),
    pieces:{...player.pieces},
    roads:[...player.roads],
    settlements:[...player.settlements],
    cities:[...player.cities],
    knightsPlayed:player.knightsPlayed||0,
    revealedVP:player.revealedVP||0,
    longestRoad:player.longestRoad||0,
    hasLongestRoad:!!player.hasLongestRoad,
    hasLargestArmy:!!player.hasLargestArmy,
    builtThisTurn:!!player.builtThisTurn,
  };
  if(!detailed) return base;
  const devCounts={};
  for(const card of player.dev||[]){
    devCounts[card]=(devCounts[card]||0)+1;
  }
  return {
    ...base,
    expectedPerTurn:cpuAnalysisResourceRates(player),
    devCounts,
    fishTokens:[...(player.fishTokens||[])],
    cpuPlan:cpuAnalysisClone(player.cpuPlan),
  };
}


function cpuAnalysisStateSnapshot(focusPlayer=null,full=false){
  if(!game) return null;
  return {
    turnSerial:game.turnSerial,
    turnNo:game.turnNo,
    current:game.current,
    phase:game.phase,
    rolled:!!game.rolled,
    dice:[...(game.turnDice||game.dice||[])],
    robberHex:game.robberHex??null,
    oldBootHolder:game.oldBootHolder??null,
    bank:{...game.bank},
    devDeckRemaining:game.devDeck?.length??0,
    focusPlayerId:focusPlayer?.id??null,
    players:game.players.map(player=>
      cpuAnalysisPlayerSnapshot(
        player,
        full || player.id===focusPlayer?.id
      )
    ),
  };
}


function cpuAnalysisDescribeVertex(vertexId){
  const vertex=game?.board?.vertices?.[vertexId];
  if(!vertex) return null;
  return {
    id:vertexId,
    hexes:vertex.hexes.map(hexId=>{
      const hex=game.board.hexes[hexId];
      return {
        id:hexId,
        resource:hex?.resource??null,
        number:hex?.number??null,
        lakeNumbers:hex?.lakeNumbers?[...hex.lakeNumbers]:null,
      };
    }),
    harbors:vertex.edges
      .map(edgeId=>game.board.edges[edgeId]?.harbor)
      .filter(Boolean),
    fishingGrounds:(game.board.fishingGrounds||[])
      .filter(ground=>ground.vertexId===vertexId)
      .map(ground=>ground.number),
    building:cpuAnalysisClone(vertex.building),
  };
}

function cpuAnalysisDescribeEdge(edgeId){
  const edge=game?.board?.edges?.[edgeId];
  if(!edge) return null;
  return {
    id:edgeId,
    a:edge.a,
    b:edge.b,
    harbor:edge.harbor??null,
    road:edge.road??null,
    endpointA:cpuAnalysisDescribeVertex(edge.a),
    endpointB:cpuAnalysisDescribeVertex(edge.b),
  };
}

function cpuAnalysisGoalSummary(player,goal,rank=null){
  if(!goal) return null;
  const contestAdjustment=goal.contest
    ?goal.contest.urgencyBonus*.75-
      goal.contest.hopelessPenalty*.85+
      (goal.denialBonus||0)*.75
    :0;
  const lookaheadBonus=Number.isFinite(goal.lookaheadBonus)
    ?goal.lookaheadBonus
    :0;
  const scoreComponents={
    base:cpuAnalysisRound(goal.base||0),
    board:cpuAnalysisRound((goal.boardScore||0)*.68),
    outcome:cpuAnalysisRound(goal.outcomeValue||0),
    contest:cpuAnalysisRound(contestAdjustment),
    distancePenalty:cpuAnalysisRound(-(goal.distance||0)*4.4),
    etaPenalty:cpuAnalysisRound(-(goal.eta||0)*7.2),
    roadOpportunityPenalty:cpuAnalysisRound(-(goal.roadOpportunityPenalty||0)),
    lookahead:cpuAnalysisRound(lookaheadBonus),
  };
  return {
    rank,
    key:cpuGoalKey(goal),
    kind:goal.kind,
    targetId:goal.targetId??null,
    expansionTargetId:goal.expansionTargetId??null,
    roadsNeeded:goal.roadsNeeded??null,
    cost:cpuAnalysisClone(goal.cost),
    planCost:cpuAnalysisClone(cpuGoalPlanCost(goal)),
    missing:cpuAnalysisRound(goal.missing),
    distance:cpuAnalysisRound(goal.distance),
    eta:cpuAnalysisRound(goal.eta),
    boardScore:cpuAnalysisRound(goal.boardScore||0),
    outcomeValue:cpuAnalysisRound(goal.outcomeValue||0),
    lookaheadScore:cpuAnalysisRound(goal.lookaheadScore),
    lookaheadBonus:cpuAnalysisRound(goal.lookaheadBonus),
    strategicScore:cpuAnalysisRound(goal.strategicScore),
    planningVP:cpuAnalysisRound(cpuPlanningVP(player)),
    hiddenVictoryPoints:cpuHiddenVictoryPointCount(player),
    scoreComponents,
    buildable:cpuGoalBuildable(player,goal),
    contest:goal.contest?cpuAnalysisClone(goal.contest):null,
    denialBonus:cpuAnalysisRound(goal.denialBonus||0),
    roadAwardPlan:goal.roadAwardPlan?cpuAnalysisClone(goal.roadAwardPlan):null,
  };
}


const cpuAnalysisAcceptedReceiptIds=new Set();
let cpuAnalysisServerUploadTimer=null;

function cpuAnalysisHumanVisibleState(player){
  if(!game || !player) return null;
  return {
    playerId:player.id,
    own:{
      publicVP:publicVP(player),
      totalVP:totalVP(player),
      victoryTarget:victoryTarget(player),
      resources:{...player.resources},
      resourceTotal:totalResources(player),
      pieces:{...player.pieces},
      roads:[...player.roads],
      settlements:[...player.settlements],
      cities:[...player.cities],
      devCount:(player.dev||[]).length,
      knightsPlayed:player.knightsPlayed||0,
      fishTokens:[...(player.fishTokens||[])],
    },
    opponents:game.players
      .filter(other=>other.id!==player.id)
      .map(other=>({
        id:other.id,
        name:other.name,
        human:!!other.human,
        publicVP:publicVP(other),
        resourceTotal:totalResources(other),
        roads:[...other.roads],
        settlements:[...other.settlements],
        cities:[...other.cities],
        devCount:(other.dev||[]).length,
        knightsPlayed:other.knightsPlayed||0,
        hasLongestRoad:!!other.hasLongestRoad,
        hasLargestArmy:!!other.hasLargestArmy,
      })),
    phase:game.phase,
    rolled:!!game.rolled,
    currentPlayerId:game.current,
    robberHex:game.robberHex??null,
    bank:{...game.bank},
  };
}

function cpuAnalysisAvailableHumanActions(player){
  if(!game || !player || !player.human) return null;

  const result={
    phase:game.phase,
    canRoll:false,
    canEndTurn:false,
    build:{
      road:[],
      settlement:[],
      city:[],
      dev:false,
    },
    bankTrades:[],
    playerTradeTargets:[],
    playableDev:[],
    fishActions:[],
  };

  if(game.phase==="setupSettlement"){
    result.build.settlement=Object.keys(game.board.vertices)
      .filter(vertexId=>canPlaceSettlement(player.id,vertexId,true));
    return result;
  }

  if(game.phase==="setupRoad"){
    result.build.road=Object.keys(game.board.edges)
      .filter(edgeId=>canPlaceRoad(player.id,edgeId,game.setupVertex));
    return result;
  }

  if(game.phase==="moveRobber"){
    result.robberHexes=game.board.hexes
      .filter(hex=>hex.id!==game.robberHex)
      .map(hex=>hex.id);
    return result;
  }

  if(game.phase==="chooseVictim"){
    result.robberVictims=robberVictimCandidates(
      game.robberHex,
      player.id
    ).map(other=>other.id);
    return result;
  }

  if(game.phase==="discard"){
    result.discardNeed=Math.floor(totalResources(player)/2);
    return result;
  }

  if(game.phase!=="turn" || game.winner!==null) return result;

  result.canRoll=!game.rolled&&!game.diceRolling;
  result.canEndTurn=!!game.rolled && game.freeRoads===0 && !game.diceRolling;

  const canBuildNormal=
    !!game.rolled &&
    !player.builtThisTurn &&
    !game.diceRolling;

  const freeRoad=game.freeRoads>0;

  if(
    freeRoad ||
    (canBuildNormal && player.pieces.road>0 && hasCost(player,COST.road))
  ){
    result.build.road=Object.keys(game.board.edges)
      .filter(edgeId=>canPlaceRoad(player.id,edgeId));
  }

  if(
    canBuildNormal &&
    player.pieces.settlement>0 &&
    hasCost(player,COST.settlement)
  ){
    result.build.settlement=Object.keys(game.board.vertices)
      .filter(vertexId=>canPlaceSettlement(player.id,vertexId,false));
  }

  if(
    canBuildNormal &&
    player.pieces.city>0 &&
    hasCost(player,COST.city)
  ){
    result.build.city=[...player.settlements]
      .filter(vertexId=>canUpgradeCity(player.id,vertexId));
  }

  result.build.dev=
    canBuildNormal &&
    !!game.devDeck.length &&
    hasCost(player,COST.dev);

  if(game.rolled){
    for(const give of RESOURCES){
      const rate=getTradeRate(player,give);
      if((player.resources[give]||0)<rate) continue;
      for(const get of RESOURCES){
        if(give!==get && (game.bank[get]||0)>0){
          result.bankTrades.push({give,get,rate});
        }
      }
    }

    result.playerTradeTargets=game.players
      .filter(other=>other.id!==player.id)
      .map(other=>({
        id:other.id,
        name:other.name,
        resourceTotal:totalResources(other),
      }));
  }

  result.playableDev=[...new Set(player.dev||[])];

  if(game.fishermen){
    for(const action of Object.keys(FISH_ACTION_COST)){
      const cost=FISH_ACTION_COST[action];
      if(!findFishPayment(player.fishTokens,cost)) continue;
      if(action==="removeRobber" && game.robberHex===null) continue;
      if(
        action==="steal" &&
        !game.players.some(other=>other.id!==player.id&&totalResources(other)>0)
      ) continue;
      if(action==="resource" && !RESOURCES.some(resource=>game.bank[resource]>0)) continue;
      if(
        action==="road" &&
        (
          player.pieces.road<=0 ||
          !Object.keys(game.board.edges).some(edgeId=>canPlaceRoad(player.id,edgeId))
        )
      ) continue;
      if(action==="dev" && !game.devDeck.length) continue;
      result.fishActions.push(action);
    }
  }

  return result;
}

function cpuAnalysisHumanReceiptId(){
  if(
    typeof crypto!=="undefined" &&
    typeof crypto.randomUUID==="function"
  ){
    return `ha-${crypto.randomUUID()}`;
  }
  return `ha-${Date.now()}-${Math.random().toString(36).slice(2)}`;
}

function cpuAnalysisQueueHumanReceipt(player,action,data={}){
  if(
    !game ||
    !player ||
    !player.human ||
    !isLocalPlayer(player)
  ){
    return null;
  }

  const receipt={
    id:cpuAnalysisHumanReceiptId(),
    schemaVersion:1,
    at:cpuAnalysisNowIso(),
    turnSerial:game.turnSerial??null,
    turnNo:game.turnNo??null,
    phase:game.phase??null,
    playerId:player.id,
    playerName:player.name,
    action,
    data:cpuAnalysisClone(data),
    available:cpuAnalysisAvailableHumanActions(player),
    visibleState:cpuAnalysisHumanVisibleState(player),
  };

  if(!Array.isArray(game.analysisReceipts)){
    game.analysisReceipts=[];
  }
  game.analysisReceipts.push(receipt);
  game.analysisReceipts=game.analysisReceipts.slice(-4);
  game.analysisReceipt=receipt;

  if(!ONLINE_MODE){
    cpuAnalysisAcceptServerReceipt(receipt);
  }

  return receipt;
}

function cpuAnalysisAcceptServerReceipt(receipt){
  if(
    !receipt?.id ||
    cpuAnalysisAcceptedReceiptIds.has(receipt.id)
  ){
    return false;
  }

  cpuAnalysisAcceptedReceiptIds.add(receipt.id);
  if(cpuAnalysisAcceptedReceiptIds.size>3000){
    const keep=[...cpuAnalysisAcceptedReceiptIds].slice(-1500);
    cpuAnalysisAcceptedReceiptIds.clear();
    keep.forEach(id=>cpuAnalysisAcceptedReceiptIds.add(id));
  }

  const player=playerById(receipt.playerId);
  const event=cpuAnalysisRecordEvent(
    "human_action",
    player,
    {
      receiptId:receipt.id,
      action:receipt.action,
      actionData:cpuAnalysisClone(receipt.data),
      available:cpuAnalysisClone(receipt.available),
      visibleState:cpuAnalysisClone(receipt.visibleState),
      acceptedAt:cpuAnalysisNowIso(),
    },
    `human-action:${receipt.id}`
  );
  if(event){
    event.turnSerial=receipt.turnSerial??event.turnSerial;
    event.turnNo=receipt.turnNo??event.turnNo;
    event.phase=receipt.phase??event.phase;
    event.playerId=receipt.playerId??event.playerId;
    event.playerName=receipt.playerName??event.playerName;
  }
  return true;
}

function cpuAnalysisCompactPlayer(player,focus=false){
  if(!player) return null;
  return {
    id:player.id,
    name:player.name,
    human:!!player.human,
    publicVP:player.publicVP??null,
    totalVP:focus?(player.totalVP??null):undefined,
    victoryTarget:focus?(player.victoryTarget??null):undefined,
    resources:focus&&player.resources?{...player.resources}:undefined,
    resourceTotal:player.resourceTotal??null,
    pieces:focus&&player.pieces?{...player.pieces}:undefined,
    roadCount:Array.isArray(player.roads)?player.roads.length:0,
    settlementCount:Array.isArray(player.settlements)?player.settlements.length:0,
    cityCount:Array.isArray(player.cities)?player.cities.length:0,
    knightsPlayed:player.knightsPlayed??0,
    hasLongestRoad:!!player.hasLongestRoad,
    hasLargestArmy:!!player.hasLargestArmy,
  };
}

function cpuAnalysisCompactState(state){
  if(!state) return null;
  const focusId=state.focusPlayerId??null;
  return {
    turnSerial:state.turnSerial??null,
    turnNo:state.turnNo??null,
    current:state.current??null,
    phase:state.phase??null,
    rolled:!!state.rolled,
    dice:Array.isArray(state.dice)?[...state.dice]:[],
    robberHex:state.robberHex??null,
    focusPlayerId:focusId,
    players:(state.players||[]).map(player=>
      cpuAnalysisCompactPlayer(player,player.id===focusId)
    ),
  };
}

function cpuAnalysisCompactFinalState(state){
  if(!state) return null;
  return {
    turnSerial:state.turnSerial??null,
    turnNo:state.turnNo??null,
    current:state.current??null,
    phase:state.phase??null,
    robberHex:state.robberHex??null,
    bank:state.bank?{...state.bank}:null,
    players:(state.players||[]).map(player=>({
      id:player.id,
      name:player.name,
      human:!!player.human,
      publicVP:player.publicVP??null,
      totalVP:player.totalVP??null,
      victoryTarget:player.victoryTarget??null,
      resources:player.resources?{...player.resources}:null,
      pieces:player.pieces?{...player.pieces}:null,
      roads:Array.isArray(player.roads)?[...player.roads]:[],
      settlements:Array.isArray(player.settlements)?[...player.settlements]:[],
      cities:Array.isArray(player.cities)?[...player.cities]:[],
      knightsPlayed:player.knightsPlayed??0,
      hasLongestRoad:!!player.hasLongestRoad,
      hasLargestArmy:!!player.hasLargestArmy,
    })),
  };
}

function cpuAnalysisCompactCandidate(candidate){
  if(!candidate) return null;
  return {
    rank:candidate.rank??null,
    key:candidate.key??null,
    kind:candidate.kind??null,
    targetId:candidate.targetId??null,
    expansionTargetId:candidate.expansionTargetId??null,
    roadsNeeded:candidate.roadsNeeded??null,
    strategicScore:candidate.strategicScore??null,
    scoreComponents:candidate.scoreComponents?{...candidate.scoreComponents}:null,
    distance:candidate.distance??null,
    eta:candidate.eta??null,
    missing:candidate.missing??null,
    buildable:!!candidate.buildable,
    contest:candidate.contest?{
      opponentDistance:candidate.contest.opponentDistance??null,
      urgencyBonus:candidate.contest.urgencyBonus??null,
      hopelessPenalty:candidate.contest.hopelessPenalty??null,
    }:null,
    lookaheadScore:candidate.lookaheadScore??null,
    lookaheadBonus:candidate.lookaheadBonus??null,
  };
}

function cpuAnalysisCompactEvent(event){
  const data=event?.data||{};
  const base={
    seq:event?.seq??null,
    at:event?.at??null,
    type:event?.type??null,
    turnSerial:event?.turnSerial??null,
    turnNo:event?.turnNo??null,
    phase:event?.phase??null,
    currentPlayerId:event?.currentPlayerId??null,
    playerId:event?.playerId??null,
    playerName:event?.playerName??null,
  };

  if(event?.type==="goal_decision"){
    return {
      ...base,
      data:{
        stage:data.stage??null,
        selectedKey:data.selectedKey??null,
        bestScoreKey:data.bestScoreKey??null,
        selectionReason:data.selectionReason??null,
        scoreGapFromBest:data.scoreGapFromBest??null,
        selected:cpuAnalysisCompactCandidate(data.selected),
        candidates:(data.candidates||[]).slice(0,2).map(cpuAnalysisCompactCandidate),
        state:cpuAnalysisCompactState(data.state),
      },
    };
  }

  if(event?.type==="human_action"){
    return {
      ...base,
      data:{
        receiptId:data.receiptId??null,
        action:data.action??null,
        actionData:cpuAnalysisClone(data.actionData),
        available:cpuAnalysisClone(data.available),
        visibleState:cpuAnalysisClone(data.visibleState),
        acceptedAt:data.acceptedAt??null,
      },
    };
  }

  if(event?.type==="cpu_action"){
    const compact=cpuAnalysisClone(data)||{};
    delete compact.stateAfter;
    return {...base,data:compact};
  }

  if(event?.type==="turn_start"){
    return null;
  }

  if(
    event?.type==="setup_settlement_decision" ||
    event?.type==="setup_road_decision"
  ){
    return {
      ...base,
      data:{
        selectedVertexId:data.selectedVertexId??null,
        selectedEdgeId:data.selectedEdgeId??null,
        candidates:(data.candidates||[]).slice(0,5).map(item=>({
          rank:item.rank??null,
          vertexId:item.vertexId??null,
          edgeId:item.edgeId??null,
          score:item.score??null,
          baseScore:item.baseScore??null,
          pairPotential:item.pairPotential??null,
        })),
        state:cpuAnalysisCompactState(data.state),
      },
    };
  }

  const copy=cpuAnalysisClone(data)||{};
  if(copy.state) copy.state=cpuAnalysisCompactState(copy.state);
  if(copy.stateBefore) copy.stateBefore=cpuAnalysisCompactState(copy.stateBefore);
  if(copy.stateAfter) copy.stateAfter=cpuAnalysisCompactState(copy.stateAfter);
  if(Array.isArray(copy.candidates)) copy.candidates=copy.candidates.slice(0,3);
  if(Array.isArray(copy.rejected)) copy.rejected=copy.rejected.slice(0,3);
  return {...base,data:copy};
}

function cpuAnalysisBuildServerPayload(record){
  if(!record) return null;
  const compactEvents=(record.events||[])
    .map(cpuAnalysisCompactEvent)
    .filter(Boolean);
  const cpuDecisionCount=compactEvents.filter(event=>
    event.type && event.type!=="human_action" &&
    (
      event.type.endsWith("_decision") ||
      event.type==="cpu_action"
    )
  ).length;
  const humanDecisionCount=compactEvents.filter(event=>event.type==="human_action").length;

  return {
    serverCompactVersion:CPU_ANALYSIS_SERVER_COMPACT_VERSION,
    schemaVersion:record.schemaVersion,
    appVersion:record.appVersion,
    cpuLogicVersion:record.cpuLogicVersion||CPU_ANALYSIS_LOGIC_VERSION,
    matchId:record.matchId,
    startedAt:record.startedAt,
    updatedAt:record.updatedAt,
    meta:{
      roomId:record.meta?.roomId??null,
      gameSessionId:record.meta?.gameSessionId??null,
      playerCount:record.meta?.playerCount??null,
      fishermen:!!record.meta?.fishermen,
      players:cpuAnalysisClone(record.meta?.players||[]),
      scoringFormula:cpuAnalysisClone(record.meta?.scoringFormula||null),
      board:cpuAnalysisClone(record.meta?.board||null),
    },
    counts:{
      events:compactEvents.length,
      cpuDecisions:cpuDecisionCount,
      humanDecisions:humanDecisionCount,
    },
    events:compactEvents,
    result:record.result?{
      status:record.result.status,
      endedAt:record.result.endedAt,
      winnerId:record.result.winnerId,
      winnerName:record.result.winnerName,
      turns:record.result.turns,
      turnSerial:record.result.turnSerial,
      finalState:cpuAnalysisCompactFinalState(record.result.finalState),
      diceHistory:cpuAnalysisClone(record.result.diceHistory||[]),
    }:null,
  };
}


function cpuAnalysisFitServerPayload(payload){
  if(!payload) return null;

  const encoder=
    typeof TextEncoder!=="undefined"
      ?new TextEncoder()
      :null;

  const byteLength=value=>{
    const raw=JSON.stringify(value);
    return encoder
      ?encoder.encode(raw).byteLength
      :raw.length;
  };

  let bytes=byteLength(payload);

  if(bytes<=1_050_000){
    payload.counts.serverBytes=bytes;
    payload.counts.compactionLevel=1;
    return payload;
  }

  // 長い対戦だけさらに軽量化。選択結果は残し、
  // 非選択候補と重複stateを減らす。
  for(const event of payload.events||[]){
    const data=event.data||{};
    if(Array.isArray(data.candidates)){
      data.candidates=data.candidates.slice(0,1);
    }
    if(Array.isArray(data.rejected)){
      data.rejected=[];
    }
    if(event.type!=="human_action"){
      delete data.stateBefore;
      delete data.stateAfter;
    }
  }

  bytes=byteLength(payload);
  payload.counts.serverBytes=bytes;
  payload.counts.compactionLevel=2;

  if(bytes<=1_150_000){
    return payload;
  }

  // 最終保険。判断そのもの・人間行動・実行CPU行動は残し、
  // 重複しやすい補助判断イベントだけ間引く。
  payload.events=(payload.events||[]).filter((event,index)=>{
    if(
      event.type==="human_action" ||
      event.type==="cpu_action" ||
      event.type==="goal_decision" ||
      event.type==="setup_settlement_decision" ||
      event.type==="setup_road_decision" ||
      event.type==="robber_decision"
    ){
      return true;
    }

    if(
      event.type==="player_trade_decision" ||
      event.type==="bank_trade_decision" ||
      event.type==="development_decision" ||
      event.type==="fish_decision" ||
      event.type==="discard_decision"
    ){
      return index%2===0;
    }

    return true;
  });

  bytes=byteLength(payload);
  payload.counts.serverBytes=bytes;
  payload.counts.compactionLevel=3;
  payload.counts.events=payload.events.length;
  return payload;
}

async function cpuAnalysisTryServerUpload(record=null){
  if(
    typeof window.cpuAnalysisServerUpload!=="function" ||
    (typeof isOnlineHost==="function" && !isOnlineHost())
  ){
    return false;
  }

  const target=record||cpuAnalysisSession;
  if(!target?.result || target.result.status!=="finished") return false;
  if(target.serverUpload?.status==="saved") return true;

  if(
    target.meta &&
    !target.meta.gameSessionId &&
    typeof onlineRoomState!=="undefined"
  ){
    target.meta.gameSessionId=onlineRoomState?.gameSessionId??null;
  }

  const payload=cpuAnalysisFitServerPayload(
    cpuAnalysisBuildServerPayload(target)
  );
  if(!payload) return false;

  target.serverUpload={
    ...(target.serverUpload||{}),
    status:"uploading",
    attemptedAt:cpuAnalysisNowIso(),
  };
  await cpuAnalysisPersistRecord(target);

  try{
    const result=await window.cpuAnalysisServerUpload(payload);
    target.serverUpload={
      status:"saved",
      savedAt:cpuAnalysisNowIso(),
      duplicate:!!result?.duplicate,
      bytes:result?.bytes??null,
    };
    await cpuAnalysisPersistRecord(target);
    return true;
  }catch(error){
    target.serverUpload={
      status:"pending",
      attemptedAt:cpuAnalysisNowIso(),
      error:String(error?.message||error||"upload failed").slice(0,240),
    };
    await cpuAnalysisPersistRecord(target);
    return false;
  }
}

function cpuAnalysisQueueServerUpload(){
  clearTimeout(cpuAnalysisServerUploadTimer);
  cpuAnalysisServerUploadTimer=setTimeout(async()=>{
    cpuAnalysisServerUploadTimer=null;
    await cpuAnalysisPersistSession(false);
    if(cpuAnalysisSession){
      await cpuAnalysisTryServerUpload(cpuAnalysisSession);
      if(
        $("cpuAnalysisModal") &&
        !$("cpuAnalysisModal").classList.contains("hidden")
      ){
        cpuAnalysisRefreshUi();
      }
    }
  },1500);
}

async function cpuAnalysisRetryPendingUploads(){
  if(
    typeof window.cpuAnalysisServerUpload!=="function" ||
    (typeof isOnlineHost==="function" && !isOnlineHost())
  ){
    return;
  }
  const records=await cpuAnalysisGetMatches();
  for(const record of records.slice(0,CPU_ANALYSIS_MAX_MATCHES)){
    if(
      record.result?.status==="finished" &&
      record.serverUpload?.status!=="saved"
    ){
      await cpuAnalysisTryServerUpload(record);
    }
  }
}

function cpuAnalysisMakeMatchId(){
  const suffix=(
    typeof crypto!=="undefined" &&
    typeof crypto.randomUUID==="function"
  )
    ?crypto.randomUUID().replace(/-/g,"").slice(0,10)
    :`${Date.now()}-${cpuAnalysisEventSeq}`;
  return `catan-${Date.now()}-${suffix}`;
}

function cpuAnalysisEnsureSession(player=null){
  if(!game || !game.players?.some(other=>!other.human)) return null;
  const boardSignature=cpuAnalysisBoardSignature();
  if(
    cpuAnalysisSession &&
    cpuAnalysisSession.meta?.boardSignature===boardSignature &&
    cpuAnalysisSession.meta?.roomId===(game.roomId??null) &&
    (
      !cpuAnalysisSession.result ||
      game.winner!==null
    )
  ){
    return cpuAnalysisSession;
  }

  cpuAnalysisDedupeKeys.clear();
  cpuAnalysisEventSeq=0;
  cpuAnalysisEventsSincePersist=0;
  cpuAnalysisLastPersistAt=Date.now();
  cpuAnalysisSession={
    schemaVersion:CPU_ANALYSIS_SCHEMA_VERSION,
    appVersion:CPU_ANALYSIS_APP_VERSION,
    cpuLogicVersion:CPU_ANALYSIS_LOGIC_VERSION,
    matchId:cpuAnalysisMakeMatchId(),
    startedAt:cpuAnalysisNowIso(),
    updatedAt:cpuAnalysisNowIso(),
    meta:{
      roomId:game.roomId??null,
      gameSessionId:(typeof onlineRoomState!=="undefined" ? onlineRoomState?.gameSessionId : null)??null,
      playerCount:game.playerCount,
      fishermen:!!game.fishermen,
      boardSignature,
      board:cpuAnalysisBoardSnapshot(),
      players:game.players.map(other=>({
        id:other.id,
        name:other.name,
        human:!!other.human,
      })),
      scoringFormula:{
        goal:"base + boardScore*0.68 + outcomeValue + contestAdjustment - distance*4.4 - eta*7.2 + lookaheadBonus",
        lookaheadDepthNormal:4,
        lookaheadDepthEndgame:5,
        note:"v1.55 CPU強化版。解析2戦を基に道路王争いの過大評価と終盤VP認識を調整。",
      },
    },
    events:[],
    result:null,
  };
  cpuAnalysisRecordEvent(
    "match_start",
    player,
    {
      state:cpuAnalysisStateSnapshot(player,true),
    },
    `match-start:${cpuAnalysisSession.matchId}`
  );
  cpuAnalysisPersistSession(false);
  return cpuAnalysisSession;
}

function cpuAnalysisRecordEvent(type,player,data={},dedupeKey=null){
  const session=cpuAnalysisEnsureSession(player);
  if(!session) return null;
  if(dedupeKey && cpuAnalysisDedupeKeys.has(dedupeKey)) return null;
  if(dedupeKey) cpuAnalysisDedupeKeys.add(dedupeKey);
  if(session.events.length>=CPU_ANALYSIS_MAX_EVENTS){
    if(!session._truncated){
      session._truncated=true;
      session.events.push({
        seq:++cpuAnalysisEventSeq,
        at:cpuAnalysisNowIso(),
        type:"analysis_truncated",
        turnSerial:game?.turnSerial??null,
        turnNo:game?.turnNo??null,
        message:`CPU解析イベントが${CPU_ANALYSIS_MAX_EVENTS}件を超えたため以降を省略`,
      });
    }
    return null;
  }
  const event={
    seq:++cpuAnalysisEventSeq,
    at:cpuAnalysisNowIso(),
    type,
    turnSerial:game?.turnSerial??null,
    turnNo:game?.turnNo??null,
    phase:game?.phase??null,
    currentPlayerId:game?.current??null,
    playerId:player?.id??null,
    playerName:player?.name??null,
    data:cpuAnalysisClone(data),
  };
  session.events.push(event);
  session.updatedAt=event.at;
  cpuAnalysisSchedulePersist();
  return event;
}

function cpuAnalysisRecordTurnStart(player){
  if(!player || player.human) return;
  const key=`turn-start:${game.turnSerial}:${player.id}`;
  cpuAnalysisRecordEvent(
    "turn_start",
    player,
    {state:cpuAnalysisStateSnapshot(player)},
    key
  );
}

function cpuAnalysisRecordGoalDecision(player,stage,selectedGoal=null){
  if(!player || player.human || !game) return;
  const goals=cpuStrategicGoals(player);
  const selected=selectedGoal||cpuChooseGoal(player);
  const selectedKey=selected?cpuGoalKey(selected):null;
  const bestKey=goals[0]?cpuGoalKey(goals[0]):null;
  const resourceSignature=RESOURCES.map(resource=>player.resources[resource]||0).join(",");
  const key=[
    "goal",
    game.turnSerial,
    player.id,
    resourceSignature,
    player.roads.length,
    player.settlements.length,
    player.cities.length,
    player.dev.length,
    game.robberHex??"none",
    selectedKey??"none",
  ].join(":");
  cpuAnalysisRecordEvent(
    "goal_decision",
    player,
    {
      stage,
      selectedKey,
      bestScoreKey:bestKey,
      selectionReason:
        selectedKey===bestKey
          ?"highest_score"
          :selectedKey
            ?"persistent_plan_or_tactical_override"
            :"no_goal",
      scoreGapFromBest:
        selected && goals[0]
          ?cpuAnalysisRound(goals[0].strategicScore-selected.strategicScore)
          :null,
      selected:selected?cpuAnalysisGoalSummary(player,selected):null,
      candidates:goals.slice(0,16).map((goal,index)=>
        cpuAnalysisGoalSummary(player,goal,index+1)
      ),
      state:cpuAnalysisStateSnapshot(player),
    },
    key
  );
}

function cpuAnalysisRecordAction(player,action,data={}){
  if(!player || player.human) return;
  cpuAnalysisRecordEvent(
    "cpu_action",
    player,
    {
      action,
      ...cpuAnalysisClone(data),
      stateAfter:cpuAnalysisStateSnapshot(player),
    }
  );
}

function cpuAnalysisRecordSetupSettlement(playerId,scored){
  const player=playerById(playerId);
  if(!player || player.human) return;
  cpuAnalysisRecordEvent(
    "setup_settlement_decision",
    player,
    {
      selectedVertexId:scored[0]?.id??null,
      candidates:scored.slice(0,20).map((item,index)=>({
        rank:index+1,
        vertexId:item.id,
        score:cpuAnalysisRound(item.score),
        baseScore:cpuAnalysisRound(item.baseScore),
        pairPotential:cpuAnalysisRound(item.pairPotential),
        target:cpuAnalysisDescribeVertex(item.id),
      })),
      state:cpuAnalysisStateSnapshot(player),
    },
    `setup-settlement:${game.setupIndex}:${playerId}`
  );
}

function cpuAnalysisRecordSetupRoad(player,scored){
  if(!player || player.human) return;
  cpuAnalysisRecordEvent(
    "setup_road_decision",
    player,
    {
      selectedEdgeId:scored[0]?.id??null,
      candidates:scored.slice(0,12).map((item,index)=>({
        rank:index+1,
        edgeId:item.id,
        score:cpuAnalysisRound(item.score),
        edge:cpuAnalysisDescribeEdge(item.id),
      })),
      state:cpuAnalysisStateSnapshot(player),
    },
    `setup-road:${game.setupIndex}:${player.id}`
  );
}

function cpuAnalysisFinalizeMatch(winner=null){
  if(!cpuAnalysisSession || cpuAnalysisSession.result) return;
  const winningPlayer=winner||(
    game?.winner!==null && game?.winner!==undefined
      ?playerById(game.winner)
      :null
  );
  cpuAnalysisSession.result={
    status:winningPlayer?"finished":"abandoned",
    endedAt:cpuAnalysisNowIso(),
    winnerId:winningPlayer?.id??null,
    winnerName:winningPlayer?.name??null,
    turns:game?.turnNo??null,
    turnSerial:game?.turnSerial??null,
    finalState:game?cpuAnalysisStateSnapshot(winningPlayer,true):null,
    diceHistory:cpuAnalysisClone(game?.diceHistory||[]),
    logHistory:cpuAnalysisClone(game?.logHistory||[]),
  };
  cpuAnalysisSession.updatedAt=cpuAnalysisSession.result.endedAt;
  cpuAnalysisPersistSession(true);
  cpuAnalysisQueueServerUpload();
}

function cpuAnalysisAbandonCurrent(reason="new_game"){
  if(!cpuAnalysisSession) return;
  if(cpuAnalysisSession.result){
    cpuAnalysisSession=null;
    cpuAnalysisDedupeKeys.clear();
    return;
  }
  cpuAnalysisSession.result={
    status:"abandoned",
    reason,
    endedAt:cpuAnalysisNowIso(),
    winnerId:null,
    winnerName:null,
    turns:game?.turnNo??null,
    turnSerial:game?.turnSerial??null,
    finalState:game?cpuAnalysisStateSnapshot(null,true):null,
    diceHistory:cpuAnalysisClone(game?.diceHistory||[]),
    logHistory:cpuAnalysisClone(game?.logHistory||[]),
  };
  cpuAnalysisPersistSession(true);
  cpuAnalysisSession=null;
  cpuAnalysisDedupeKeys.clear();
}

function cpuAnalysisOpenDb(){
  if(typeof indexedDB==="undefined") return Promise.resolve(null);
  return new Promise(resolve=>{
    let request;
    try{
      request=indexedDB.open(CPU_ANALYSIS_DB_NAME,CPU_ANALYSIS_DB_VERSION);
    }catch(_error){
      resolve(null);
      return;
    }
    request.onupgradeneeded=()=>{
      const db=request.result;
      if(!db.objectStoreNames.contains(CPU_ANALYSIS_STORE)){
        const store=db.createObjectStore(CPU_ANALYSIS_STORE,{keyPath:"matchId"});
        store.createIndex("startedAt","startedAt",{unique:false});
      }
    };
    request.onsuccess=()=>resolve(request.result);
    request.onerror=()=>resolve(null);
  });
}

async function cpuAnalysisPersistRecord(record){
  const db=await cpuAnalysisOpenDb();
  if(!db || !record?.matchId) return false;
  const payload=cpuAnalysisClone(record);
  return new Promise(resolve=>{
    try{
      const tx=db.transaction(CPU_ANALYSIS_STORE,"readwrite");
      tx.objectStore(CPU_ANALYSIS_STORE).put(payload);
      tx.oncomplete=()=>{
        db.close();
        resolve(true);
      };
      tx.onerror=()=>{
        db.close();
        resolve(false);
      };
      tx.onabort=()=>{
        db.close();
        resolve(false);
      };
    }catch(_error){
      db.close();
      resolve(false);
    }
  });
}

function cpuAnalysisSchedulePersist(){
  cpuAnalysisEventsSincePersist++;
  const now=Date.now();
  const dueByCount=cpuAnalysisEventsSincePersist>=45;
  const dueByTime=!cpuAnalysisLastPersistAt || now-cpuAnalysisLastPersistAt>=60000;
  if(!dueByCount && !dueByTime) return;
  if(cpuAnalysisPersistTimer) return;
  cpuAnalysisPersistTimer=setTimeout(()=>{
    cpuAnalysisPersistTimer=null;
    cpuAnalysisPersistSession(false);
  },800);
}


async function cpuAnalysisPersistSession(prune=false){
  if(!cpuAnalysisSession) return false;
  const saved=await cpuAnalysisPersistRecord(cpuAnalysisSession);
  if(saved){
    cpuAnalysisEventsSincePersist=0;
    cpuAnalysisLastPersistAt=Date.now();
  }
  if(saved && prune) await cpuAnalysisPruneOldMatches();
  if($("cpuAnalysisModal") && !$("cpuAnalysisModal").classList.contains("hidden")){
    cpuAnalysisRefreshUi();
  }
  return saved;
}

async function cpuAnalysisGetMatches(){
  const db=await cpuAnalysisOpenDb();
  if(!db) return cpuAnalysisSession?[cpuAnalysisClone(cpuAnalysisSession)]:[];
  const records=await new Promise(resolve=>{
    try{
      const tx=db.transaction(CPU_ANALYSIS_STORE,"readonly");
      const request=tx.objectStore(CPU_ANALYSIS_STORE).getAll();
      request.onsuccess=()=>resolve(request.result||[]);
      request.onerror=()=>resolve([]);
    }catch(_error){
      resolve([]);
    }
  });
  db.close();
  if(cpuAnalysisSession){
    const current=cpuAnalysisClone(cpuAnalysisSession);
    const existingIndex=records.findIndex(record=>record.matchId===cpuAnalysisSession.matchId);
    if(existingIndex>=0){
      records[existingIndex]=current;
    }else{
      records.push(current);
    }
  }
  return records.sort((a,b)=>String(b.startedAt||"").localeCompare(String(a.startedAt||"")));
}

async function cpuAnalysisDeleteMatch(matchId){
  const db=await cpuAnalysisOpenDb();
  if(db){
    await new Promise(resolve=>{
      try{
        const tx=db.transaction(CPU_ANALYSIS_STORE,"readwrite");
        tx.objectStore(CPU_ANALYSIS_STORE).delete(matchId);
        tx.oncomplete=()=>resolve();
        tx.onerror=()=>resolve();
      }catch(_error){ resolve(); }
    });
    db.close();
  }
  if(cpuAnalysisSession?.matchId===matchId){
    cpuAnalysisSession=null;
    cpuAnalysisDedupeKeys.clear();
  }
}

async function cpuAnalysisClearAll(){
  const db=await cpuAnalysisOpenDb();
  if(db){
    await new Promise(resolve=>{
      try{
        const tx=db.transaction(CPU_ANALYSIS_STORE,"readwrite");
        tx.objectStore(CPU_ANALYSIS_STORE).clear();
        tx.oncomplete=()=>resolve();
        tx.onerror=()=>resolve();
      }catch(_error){ resolve(); }
    });
    db.close();
  }
  cpuAnalysisSession=null;
  cpuAnalysisDedupeKeys.clear();
}

async function cpuAnalysisPruneOldMatches(){
  const records=await cpuAnalysisGetMatches();
  const extra=records.slice(CPU_ANALYSIS_MAX_MATCHES);
  for(const record of extra){
    await cpuAnalysisDeleteMatch(record.matchId);
  }
}

function cpuAnalysisCsvEscape(value){
  const text=value===null||value===undefined?"":String(value);
  return `"${text.replace(/"/g,'""')}"`;
}

function cpuAnalysisMatchToCsv(match){
  const header=[
    "matchId","appVersion","winner","eventSeq","turnSerial","turnNo","stage",
    "cpuId","cpuName","cpuVP","targetVP","wood","brick","wool","grain","ore",
    "rank","selected","selectionReason","kind","key","targetId","expansionTargetId","roadsNeeded",
    "strategicScore","base","boardComponent","outcomeComponent","contestComponent",
    "distancePenalty","etaPenalty","lookaheadBonus","lookaheadScore","distance","eta","missing","buildable"
  ];
  const rows=[header];
  for(const event of match.events||[]){
    if(event.type!=="goal_decision") continue;
    const data=event.data||{};
    const focus=(data.state?.players||[]).find(player=>player.id===event.playerId)||{};
    for(const candidate of data.candidates||[]){
      rows.push([
        match.matchId,
        match.appVersion,
        match.result?.winnerName||"",
        event.seq,
        event.turnSerial,
        event.turnNo,
        data.stage||"",
        event.playerId,
        event.playerName,
        focus.totalVP??"",
        focus.victoryTarget??"",
        focus.resources?.wood??0,
        focus.resources?.brick??0,
        focus.resources?.wool??0,
        focus.resources?.grain??0,
        focus.resources?.ore??0,
        candidate.rank??"",
        candidate.key===data.selectedKey?1:0,
        data.selectionReason||"",
        candidate.kind||"",
        candidate.key||"",
        candidate.targetId??"",
        candidate.expansionTargetId??"",
        candidate.roadsNeeded??"",
        candidate.strategicScore??"",
        candidate.scoreComponents?.base??"",
        candidate.scoreComponents?.board??"",
        candidate.scoreComponents?.outcome??"",
        candidate.scoreComponents?.contest??"",
        candidate.scoreComponents?.distancePenalty??"",
        candidate.scoreComponents?.etaPenalty??"",
        candidate.scoreComponents?.lookahead??"",
        candidate.lookaheadScore??"",
        candidate.distance??"",
        candidate.eta??"",
        candidate.missing??"",
        candidate.buildable?1:0,
      ]);
    }
  }
  return rows.map(row=>row.map(cpuAnalysisCsvEscape).join(",")).join("\r\n");
}

function cpuAnalysisSafeFilename(text){
  return String(text||"analysis").replace(/[^0-9A-Za-z_\-.]/g,"_");
}

function cpuAnalysisSaveText(filename,text,mime){
  const blob=new Blob([text],{type:mime});
  const url=URL.createObjectURL(blob);
  const anchor=document.createElement("a");
  anchor.href=url;
  anchor.download=filename;
  document.body.appendChild(anchor);
  anchor.click();
  anchor.remove();
  setTimeout(()=>URL.revokeObjectURL(url),1500);
}

async function cpuAnalysisExportMatch(matchId,format="json"){
  await cpuAnalysisPersistSession(false);
  const records=await cpuAnalysisGetMatches();
  const match=records.find(record=>record.matchId===matchId)||records[0];
  if(!match) return false;
  const stamp=String(match.startedAt||"").replace(/[:.]/g,"-");
  if(format==="csv"){
    cpuAnalysisSaveText(
      `catan_cpu_${cpuAnalysisSafeFilename(stamp)}_${cpuAnalysisSafeFilename(match.matchId)}.csv`,
      cpuAnalysisMatchToCsv(match),
      "text/csv;charset=utf-8"
    );
  }else{
    cpuAnalysisSaveText(
      `catan_cpu_${cpuAnalysisSafeFilename(stamp)}_${cpuAnalysisSafeFilename(match.matchId)}.json`,
      JSON.stringify(match,null,2),
      "application/json;charset=utf-8"
    );
  }
  return true;
}

async function cpuAnalysisExportAll(){
  await cpuAnalysisPersistSession(false);
  const records=await cpuAnalysisGetMatches();
  if(!records.length) return false;
  cpuAnalysisSaveText(
    `catan_cpu_all_${Date.now()}.json`,
    JSON.stringify({
      schemaVersion:CPU_ANALYSIS_SCHEMA_VERSION,
      appVersion:CPU_ANALYSIS_APP_VERSION,
      exportedAt:cpuAnalysisNowIso(),
      matches:records,
    },null,2),
    "application/json;charset=utf-8"
  );
  return true;
}


async function cpuAnalysisRefreshServerUi(){
  const status=$("cpuAnalysisServerStatus");
  if(!status) return;

  if(typeof window.cpuAnalysisServerStats!=="function"){
    status.textContent="サーバー解析：利用できません";
    return;
  }

  status.textContent="サーバー解析：確認中...";
  try{
    const data=await window.cpuAnalysisServerStats();
    const stats=data.stats||{};
    status.textContent=
      `サーバー保存ゲーム：${stats.games||0}件`+
      `｜CPU判断：${stats.cpuDecisions||0}`+
      `｜人間判断：${stats.humanDecisions||0}`+
      `｜保存量：約${Math.round((stats.bytes||0)/1024)}KB`;
  }catch(error){
    status.textContent=
      `サーバー解析：${String(error?.message||error||"取得失敗")}`;
  }
}

async function cpuAnalysisExportServerAll(){
  if(
    typeof window.cpuAnalysisServerList!=="function" ||
    typeof window.cpuAnalysisServerFetchMatch!=="function"
  ){
    return false;
  }

  const status=$("cpuAnalysisServerStatus");
  try{
    if(status) status.textContent="サーバー解析：一括JSONを取得中...";
    const listData=await window.cpuAnalysisServerList();
    const items=listData.matches||[];
    const matches=[];

    for(let index=0;index<items.length;index++){
      if(status){
        status.textContent=
          `サーバー解析：${index+1}/${items.length}件を取得中...`;
      }
      const result=await window.cpuAnalysisServerFetchMatch(items[index].matchId);
      if(result?.match) matches.push(result.match);
    }

    cpuAnalysisSaveText(
      `catan_cpu_server_all_${Date.now()}.json`,
      JSON.stringify({
        schemaVersion:CPU_ANALYSIS_SCHEMA_VERSION,
        appVersion:CPU_ANALYSIS_APP_VERSION,
        cpuLogicVersion:CPU_ANALYSIS_LOGIC_VERSION,
        exportedAt:cpuAnalysisNowIso(),
        source:"cloudflare-analysis-store",
        matches,
      },null,2),
      "application/json;charset=utf-8"
    );

    await cpuAnalysisRefreshServerUi();
    return true;
  }catch(error){
    if(status){
      status.textContent=
        `サーバー解析：一括出力失敗 - ${String(error?.message||error)}`;
    }
    return false;
  }
}

function cpuAnalysisFormatStartedAt(value){
  if(!value) return "日時不明";
  const date=new Date(value);
  if(Number.isNaN(date.getTime())) return value;
  return date.toLocaleString("ja-JP");
}

async function cpuAnalysisRefreshUi(){
  const list=$("cpuAnalysisMatchList");
  const status=$("cpuAnalysisStatus");
  if(!list || !status) return;
  const records=await cpuAnalysisGetMatches();
  const currentEvents=cpuAnalysisSession?.events?.length||0;
  status.textContent=`ローカル保存：${records.length}件${cpuAnalysisSession&&!cpuAnalysisSession.result?`｜現在記録中：${currentEvents}イベント`:""}`;
  if(!records.length){
    list.innerHTML='<p class="cpu-analysis-empty">まだCPU解析データはありません。</p>';
    return;
  }
  list.innerHTML=records.map(record=>{
    const result=record.result;
    const statusText=result?.status==="finished"
      ?`勝者：${result.winnerName||"不明"}`
      :result?.status==="abandoned"
        ?"中断"
        :"記録中";
    const cpuNames=(record.meta?.players||[]).filter(player=>!player.human).map(player=>player.name).join(" / ")||"CPUなし";
    return `
      <article class="cpu-analysis-match" data-analysis-match="${record.matchId}">
        <div class="cpu-analysis-match-main">
          <strong>${cpuAnalysisFormatStartedAt(record.startedAt)}</strong>
          <span>${record.appVersion||""}｜${record.meta?.playerCount||"?"}人${record.meta?.fishermen?"・漁師":""}｜${statusText}</span>
          <small>${cpuNames}｜イベント ${(record.events||[]).length}件</small>
        </div>
        <div class="cpu-analysis-match-actions">
          <button type="button" data-analysis-export="json" data-match-id="${record.matchId}">JSON</button>
          <button type="button" class="secondary" data-analysis-export="csv" data-match-id="${record.matchId}">CSV</button>
          <button type="button" class="danger" data-analysis-delete="${record.matchId}">削除</button>
        </div>
      </article>`;
  }).join("");
}

function cpuAnalysisOpenModal(){
  const modal=$("cpuAnalysisModal");
  if(!modal) return;
  modal.classList.remove("hidden");
  cpuAnalysisRefreshUi();
  cpuAnalysisRefreshServerUi();
  cpuAnalysisRetryPendingUploads();
}

function cpuAnalysisCloseModal(){
  $("cpuAnalysisModal")?.classList.add("hidden");
}

function initCpuAnalysisUi(){
  document.querySelectorAll("[data-open-cpu-analysis]").forEach(button=>{
    button.addEventListener("click",cpuAnalysisOpenModal);
  });
  $("cpuAnalysisCloseBtn")?.addEventListener("click",cpuAnalysisCloseModal);
  $("cpuAnalysisModal")?.addEventListener("click",event=>{
    if(event.target===$("cpuAnalysisModal")) cpuAnalysisCloseModal();
  });
  $("cpuAnalysisExportLatestJson")?.addEventListener("click",async()=>{
    const records=await cpuAnalysisGetMatches();
    if(records[0]) cpuAnalysisExportMatch(records[0].matchId,"json");
  });
  $("cpuAnalysisExportLatestCsv")?.addEventListener("click",async()=>{
    const records=await cpuAnalysisGetMatches();
    if(records[0]) cpuAnalysisExportMatch(records[0].matchId,"csv");
  });
  $("cpuAnalysisExportAllJson")?.addEventListener("click",cpuAnalysisExportAll);
  $("cpuAnalysisExportServerAllJson")?.addEventListener(
    "click",
    cpuAnalysisExportServerAll
  );
  $("cpuAnalysisRetryUpload")?.addEventListener("click",async()=>{
    await cpuAnalysisRetryPendingUploads();
    await cpuAnalysisRefreshUi();
    await cpuAnalysisRefreshServerUi();
  });
  $("cpuAnalysisClearServer")?.addEventListener("click",async()=>{
    if(
      typeof window.cpuAnalysisServerClear!=="function" ||
      !confirm("サーバーに保存されたカタン解析ログをすべて削除しますか？")
    ){
      return;
    }
    try{
      await window.cpuAnalysisServerClear();
      await cpuAnalysisRefreshServerUi();
    }catch(error){
      const status=$("cpuAnalysisServerStatus");
      if(status) status.textContent=`サーバー解析：削除失敗 - ${String(error?.message||error)}`;
    }
  });
  $("cpuAnalysisClearAll")?.addEventListener("click",async()=>{
    if(!confirm("保存済みのCPU解析データをすべて削除しますか？")) return;
    await cpuAnalysisClearAll();
    cpuAnalysisRefreshUi();
  });
  $("cpuAnalysisMatchList")?.addEventListener("click",async event=>{
    const exportButton=event.target.closest("[data-analysis-export]");
    if(exportButton){
      cpuAnalysisExportMatch(exportButton.dataset.matchId,exportButton.dataset.analysisExport);
      return;
    }
    const deleteButton=event.target.closest("[data-analysis-delete]");
    if(deleteButton){
      if(!confirm("この対戦のCPU解析データを削除しますか？")) return;
      await cpuAnalysisDeleteMatch(deleteButton.dataset.analysisDelete);
      cpuAnalysisRefreshUi();
    }
  });
}

const HEX_DIRECTIONS = [
  [1,0], [1,-1], [0,-1], [-1,0], [-1,1], [0,1]
];

// 数値トークン裏面のA→R順
const NUMBER_SEQUENCE_3_4 = [
  5,2,6,3,8,10,9,12,11,4,8,10,9,4,5,6,3,11
];

// 5～6人用トークン裏面のA→Y→Za→Zb→Zc順
const NUMBER_SEQUENCE_5_6 = [
  2,5,4,6,3,9,8,11,11,10,6,3,8,4,
  8,10,11,12,10,5,4,9,5,9,12,3,2,6
];

function axialKey(coord){
  return `${coord.q},${coord.r}`;
}

function axialPosition(coord){
  return {
    x:Math.sqrt(3)*(coord.q+coord.r/2),
    y:1.5*coord.r,
  };
}

function angleDistance(a,b){
  return Math.abs(((a-b+Math.PI)%(Math.PI*2))-Math.PI);
}

function createNumberSpiral(axial,startCoord){
  const remaining=new Map(axial.map(c=>[axialKey(c),c]));
  const center=axial.reduce((sum,c)=>{
    const p=axialPosition(c);
    sum.x+=p.x;
    sum.y+=p.y;
    return sum;
  },{x:0,y:0});
  center.x/=axial.length;
  center.y/=axial.length;

  const startPos=axialPosition(startCoord);
  const startAngle=Math.atan2(startPos.y-center.y,startPos.x-center.x);
  const order=[];
  let firstLayer=true;

  while(remaining.size){
    const cells=[...remaining.values()];
    const boundary=cells.filter(c=>{
      let neighbors=0;
      for(const [dq,dr] of HEX_DIRECTIONS){
        if(remaining.has(`${c.q+dq},${c.r+dr}`)) neighbors++;
      }
      return neighbors<6;
    });

    if(boundary.length===1){
      order.push(boundary[0]);
      break;
    }

    const angleOf=c=>{
      const p=axialPosition(c);
      return Math.atan2(p.y-center.y,p.x-center.x);
    };

    // 画面座標では降順が見た目の反時計回り
    boundary.sort((a,b)=>angleOf(b)-angleOf(a));

    let layerStart;
    if(firstLayer){
      layerStart=startCoord;
      firstLayer=false;
    }else{
      layerStart=boundary.slice().sort((a,b)=>{
        const da=angleDistance(angleOf(a),startAngle);
        const db=angleDistance(angleOf(b),startAngle);
        if(Math.abs(da-db)>1e-9) return da-db;
        const pa=axialPosition(a),pb=axialPosition(b);
        return Math.hypot(pa.x-center.x,pa.y-center.y)-
               Math.hypot(pb.x-center.x,pb.y-center.y);
      })[0];
    }

    const startIndex=boundary.findIndex(c=>axialKey(c)===axialKey(layerStart));
    const rotated=[
      ...boundary.slice(startIndex),
      ...boundary.slice(0,startIndex),
    ];
    order.push(...rotated);
    rotated.forEach(c=>remaining.delete(axialKey(c)));
  }

  return order;
}

function createSvg(tag, attrs={}){
  const el=document.createElementNS(NS,tag);
  for(const [k,v] of Object.entries(attrs)) el.setAttribute(k,v);
  return el;
}

function preloadTileImages(){
  if(preloadedTileImages.length) return;

  for(const resource of ["wood","brick","wool","grain","ore","desert","lake"]){
    const image=new Image();
    let triedPng=false;
    image.decoding="async";
    image.addEventListener("error",()=>{
      if(!triedPng){
        triedPng=true;
        image.src=`${TILE_IMAGE_PATH}/${resource}.png`;
      }
    });
    image.src=`${TILE_IMAGE_PATH}/${resource}.webp`;
    preloadedTileImages.push(image);
  }
}


const AWARD_PRESENTATION = {
  oldBoot:{
    title:"ボロ靴をゲット！",
    fallback:"🥾",
    asset:"old-boot",
  },
  largestArmy:{
    title:"最大騎士団",
    fallback:"⚔️",
    asset:"largest-army",
  },
  longestRoad:{
    title:"最長交易路",
    fallback:"🛣️",
    asset:"longest-road",
  },
  devDraw:{
    title:"発展カードを引きました",
    fallback:"🎴",
    asset:"development-card",
  },
  devKnight:{
    title:"騎士が盗賊を追いやった！",
    fallback:"🐴",
    asset:"dev-knight",
    playerSuffix:"の",
    textBeforeImage:true,
  },
  devMonopoly:{
    title:"資源を独占！？",
    fallback:"👑",
    asset:"dev-monopoly",
    playerSuffix:"が",
    textBeforeImage:true,
  },
  devDiscovery:{
    title:"資源を二つ発見！",
    fallback:"✨",
    asset:"dev-discovery",
    playerSuffix:"が",
    textBeforeImage:true,
  },
  devRoadBuilding:{
    title:"街道を二本建てる！！",
    fallback:"🛣️",
    asset:"dev-road-building",
    playerSuffix:"が",
    textBeforeImage:true,
  },
  devVictoryPoint:{
    title:"勝利点",
    fallback:"⭐",
    asset:"dev-victory-point",
  },
  robberAppears:{
    title:"盗賊が現れた！",
    fallback:"🐱",
    asset:"robber",
    hidePlayer:true,
    textBeforeImage:true,
    scene:"robberShake",
  },
  fishRemoveRobber:{
    title:"盗賊を追い払った！",
    fallback:"🐟",
    asset:"fish-remove-robber",
    playerSuffix:"が",
    textBeforeImage:true,
    scene:"fishChase",
  },
  fishSteal:{
    title:"資源を奪った！",
    fallback:"🎴",
    asset:"fish-steal",
    textBeforeImage:true,
  },
};

function queueAwardEvent(type,playerId=null,details={}){
  if(!game || !AWARD_PRESENTATION[type]) return;

  const player=
    playerId===null || playerId===undefined
      ?null
      :playerById(playerId);

  if(
    playerId!==null &&
    playerId!==undefined &&
    !player
  ){
    return;
  }

  if(!Array.isArray(game.awardEvents)){
    game.awardEvents=[];
  }

  game.awardEvents.push({
    id:`${type}-${playerId??"system"}-${Date.now()}-${Math.random().toString(36).slice(2)}`,
    type,
    playerId,
    playerName:player?.name||"",
    playerColor:player?.color||"#ffffff",
    ...details,
    createdAt:Date.now(),
  });

  game.awardEvents=game.awardEvents.slice(-32);
}

function collectAwardAnnouncements(){
  if(!game || !Array.isArray(game.awardEvents)) return;

  for(const event of game.awardEvents){
    if(!event?.id || shownAwardEventIds.has(event.id)) continue;
    shownAwardEventIds.add(event.id);
    awardDisplayQueue.push(event);
  }

  playNextAwardAnnouncement();
}

function hideAwardAnnouncement(){
  clearTimeout(awardDisplayTimer);
  awardDisplayTimer=null;
  $("awardAnnouncement")?.classList.add("hidden");
  awardDisplayActive=false;
  playNextAwardAnnouncement();
}

function awardSceneHtml(scene){
  if(scene==="robberShake"){
    return `<div class="robber-shake-scene">
      <span class="robber-shake-icon">🐱</span>
    </div>`;
  }

  if(scene==="fishChase"){
    return `<div class="fish-chase-scene">
      <span class="thrown-fish-icon">🐟</span>
      <span class="chasing-robber-icon">🐱</span>
      <span class="fish-throw-spark">💨</span>
    </div>`;
  }

  return "";
}

function playNextAwardAnnouncement(){
  if(awardDisplayActive || !awardDisplayQueue.length) return;

  const event=awardDisplayQueue.shift();
  const meta=AWARD_PRESENTATION[event.type];
  const overlay=$("awardAnnouncement");

  if(!meta || !overlay){
    awardDisplayActive=false;
    playNextAwardAnnouncement();
    return;
  }

  awardDisplayActive=true;

  const card=$("awardAnnouncementCard");
  const playerName=$("awardAnnouncementPlayer");
  const title=$("awardAnnouncementTitle");
  const image=$("awardAnnouncementImage");
  const fallback=$("awardAnnouncementFallback");
  const scene=$("awardAnnouncementScene");

  card.className=`award-announcement-card type-${event.type}`;
  card.classList.toggle(
    "announcement-text-before-image",
    !!meta.textBeforeImage
  );
  card.style.borderColor=
    event.type==="robberAppears"
      ?"#ffffff"
      :(event.playerColor||"#ffffff");

  const basePlayerName=
    event.playerName||
    (
      event.playerId!==null &&
      event.playerId!==undefined
        ?playerById(event.playerId)?.name
        :""
    )||
    "プレイヤー";

  const playerLine=
    event.playerLine ??
    (
      meta.hidePlayer
        ?""
        :`${basePlayerName}${meta.playerSuffix||""}`
    );

  playerName.textContent=playerLine;
  playerName.classList.toggle("hidden",!playerLine);
  title.textContent=event.title||meta.title;

  image.onload=null;
  image.onerror=null;
  image.classList.add("hidden");
  fallback.classList.add("hidden");
  scene.className="award-announcement-scene hidden";
  scene.innerHTML="";

  if(meta.scene){
    scene.innerHTML=awardSceneHtml(meta.scene);
    scene.classList.remove("hidden");
    scene.classList.add(`scene-${meta.scene}`);
  }else{
    fallback.textContent=meta.fallback;
    fallback.classList.remove("hidden");
    image.alt=`${event.title||meta.title}の画像`;

    const candidates=[
      `assets/awards/${meta.asset}.webp`,
      `assets/awards/${meta.asset}.png`,
      `assets/awards/${meta.asset}.svg`,
    ];

    let candidateIndex=0;

    image.onload=()=>{
      image.classList.remove("hidden");
      fallback.classList.add("hidden");
    };

    image.onerror=()=>{
      candidateIndex++;
      if(candidateIndex<candidates.length){
        image.src=candidates[candidateIndex];
      }else{
        image.classList.add("hidden");
        fallback.classList.remove("hidden");
      }
    };

    image.src=candidates[candidateIndex];
  }

  overlay.classList.remove("hidden");

  card.style.animation="none";
  void card.offsetWidth;
  card.style.animation="";

  awardDisplayTimer=setTimeout(
    hideAwardAnnouncement,
    2000
  );
}

function log(msg){
  if(game){
    if(!Array.isArray(game.logHistory)) game.logHistory=[];
    game.logHistory.unshift(msg);
    game.logHistory=game.logHistory.slice(0,160);
  }
  renderLog();
}

function renderLog(){
  const lines=game?.logHistory||[];
  const html=lines
    .map(
      msg=>
        `<div class="log-line">`+
        `${escapeHtml(msg)}`+
        `</div>`
    )
    .join("");

  const box=$("log");
  if(box) box.innerHTML=html;

  const desktopBox=$("desktopLogContent");
  if(desktopBox) desktopBox.innerHTML=html;
}

function escapeHtml(value){
  return String(value)
    .replaceAll("&","&amp;")
    .replaceAll("<","&lt;")
    .replaceAll(">","&gt;")
    .replaceAll('"',"&quot;");
}


function closeChoiceModal(){
  const modal=$("choiceModal");
  if(modal) modal.classList.add("hidden");
  choiceModalState=null;
}

function openChoiceModal({
  title,
  guide="",
  options=[],
  onSelect,
  allowCancel=true,
  cancelText="戻る",
  onCancel=null,
}){
  choiceModalState={onSelect,onCancel};
  $("choiceTitle").textContent=title;
  $("choiceGuide").textContent=guide;
  $("choiceCancelBtn").textContent=cancelText;
  $("choiceCancelBtn").classList.toggle("hidden",!allowCancel);
  $("choiceOptions").innerHTML=options.map((option,index)=>`
    <button
      class="choice-option ${option.className||""}"
      data-choice-index="${index}"
      ${option.disabled?"disabled":""}
    >
      ${option.icon?`<span class="choice-option-icon">${option.icon}</span>`:""}
      <span class="choice-option-label">${option.label}</span>
      ${option.sub?`<span class="choice-option-sub">${option.sub}</span>`:""}
    </button>
  `).join("");
  document.querySelectorAll("[data-choice-index]").forEach(button=>{
    button.addEventListener("click",()=>{
      const option=options[Number(button.dataset.choiceIndex)];
      const callback=choiceModalState?.onSelect;
      closeChoiceModal();
      if(typeof callback==="function") callback(option.value,option);
    });
  });
  $("choiceModal").classList.remove("hidden");
}

function openConfirmModal(title,guide,onYes){
  openChoiceModal({
    title,
    guide,
    allowCancel:false,
    options:[
      {value:true,label:"YES",icon:"✓",className:"yes"},
      {value:false,label:"NO",icon:"×",className:"no"},
    ],
    onSelect:value=>{ if(value && typeof onYes==="function") onYes(); },
  });
}

function removeBoardSnapshot(){
  svg?.parentElement
    ?.querySelector(".board-snapshot")
    ?.remove();
}

function clearPlacementPreview(){
  pendingPlacementPreview=null;
  removeBoardSnapshot();
}

function requestPlacementConfirmation({
  kind,
  targetId,
  itemName,
  guide="",
  onConfirm,
}){
  if(pendingPlacementPreview) return;

  pendingPlacementPreview={
    kind,
    targetId,
    playerId:currentPlayer()?.id??null,
    playerColor:currentPlayer()?.color||"#ffffff",
    itemName,
  };

  /*
    仮置き表示をすぐ見せるため、
    盤面更新時の一時スナップショットは使わない。
  */
  removeBoardSnapshot();
  render();

  openChoiceModal({
    title:"ここに置いていいですか？",
    guide:
      guide||
      `${itemName}を選択した場所に置きます。`,
    allowCancel:false,
    options:[
      {
        value:true,
        label:"はい",
        icon:"✓",
        className:"yes",
        sub:"この場所で確定する",
      },
      {
        value:false,
        label:"いいえ",
        icon:"×",
        className:"no",
        sub:"場所を選び直す",
      },
    ],
    onSelect:confirmed=>{
      clearPlacementPreview();

      if(
        confirmed &&
        typeof onConfirm==="function"
      ){
        onConfirm();
      }else{
        render();
      }
    },
  });
}

function placementPreviewMatches(kind,targetId){
  return (
    pendingPlacementPreview?.kind===kind &&
    String(pendingPlacementPreview.targetId)===String(targetId)
  );
}

function confirmStealTarget(
  targetId,
  onConfirm,
  onReject=null
){
  const target=playerById(targetId);

  if(!target){
    if(typeof onReject==="function"){
      onReject();
    }
    return;
  }

  openChoiceModal({
    title:"この人から奪っていいですか？",
    guide:
      `${target.name}から資源を`+
      "ランダムに1枚奪います。",
    allowCancel:false,
    options:[
      {
        value:true,
        label:"はい",
        icon:"✓",
        className:"yes",
        sub:`${target.name}から奪う`,
      },
      {
        value:false,
        label:"いいえ",
        icon:"×",
        className:"no",
        sub:"相手を選び直す",
      },
    ],
    onSelect:confirmed=>{
      if(
        confirmed &&
        typeof onConfirm==="function"
      ){
        onConfirm(target.id);
      }else if(typeof onReject==="function"){
        onReject();
      }
    },
  });
}

function playerChoiceOptions(players,subBuilder=null){
  return players.map(player=>({
    value:player.id,
    label:player.name,
    icon:`<span class="player-dot" style="display:inline-block;background:${player.color}"></span>`,
    sub:typeof subBuilder==="function"?subBuilder(player):"",
  }));
}

function openPlayerChoice(title,guide,players,onSelect,{allowCancel=true}={}){
  openChoiceModal({
    title,
    guide,
    options:playerChoiceOptions(players),
    onSelect,
    allowCancel,
  });
}

function openResourceChoice(title,guide,onSelect,{amountLabel="銀行在庫",filter=null}={}){
  const options=RESOURCES.map(resource=>({
    value:resource,
    label:RESOURCE_JA[resource],
    icon:RESOURCE_ICON[resource],
    sub:typeof amountLabel==="function"
      ? amountLabel(resource)
      : `${amountLabel}：${game.bank[resource]}枚`,
    disabled:typeof filter==="function"?!filter(resource):game.bank[resource]<=0,
  }));
  openChoiceModal({title,guide,options,onSelect,allowCancel:true});
}

function hideTurnAnnouncement(){
  clearTimeout(turnAnnouncementTimer);
  turnAnnouncementTimer=null;
  $("turnAnnouncement")?.classList.add("hidden");
}

function renderTurnAnnouncementEvent(event){
  if(!event) return;

  const overlay=$("turnAnnouncement");
  const card=$("turnAnnouncementCard");
  const text=$("turnAnnouncementText");

  if(!overlay || !card || !text) return;

  clearTimeout(turnAnnouncementTimer);

  const playerName=
    event.playerName||
    playerById(event.playerId)?.name||
    "プレイヤー";

  text.textContent=`${playerName}のターン`;
  card.style.setProperty(
    "--turn-player-color",
    event.playerColor||"#ffffff"
  );

  overlay.classList.remove("hidden");

  card.style.animation="none";
  void card.offsetWidth;
  card.style.animation="";

  turnAnnouncementTimer=setTimeout(
    hideTurnAnnouncement,
    2000
  );
}

function collectTurnAnnouncementEvents(){
  if(
    !game ||
    !Array.isArray(game.turnAnnouncementEvents)
  ){
    return;
  }

  for(const event of game.turnAnnouncementEvents){
    if(
      !event?.id ||
      shownTurnAnnouncementEventIds.has(event.id)
    ){
      continue;
    }

    shownTurnAnnouncementEventIds.add(event.id);
    renderTurnAnnouncementEvent(event);
  }
}

function queueTurnAnnouncement(playerId){
  if(!game) return;

  const player=playerById(playerId);
  if(!player) return;

  if(!Array.isArray(game.turnAnnouncementEvents)){
    game.turnAnnouncementEvents=[];
  }

  const eventId=
    `turn-${game.turnSerial}-${playerId}`;

  if(
    game.turnAnnouncementEvents.some(
      event=>event?.id===eventId
    )
  ){
    return;
  }

  game.turnAnnouncementEvents.push({
    id:eventId,
    turnSerial:game.turnSerial,
    playerId,
    playerName:player.name,
    playerColor:player.color,
    createdAt:Date.now(),
  });

  game.turnAnnouncementEvents=
    game.turnAnnouncementEvents.slice(-32);
}

function normalizedResourceDelta(delta){
  if(!delta || typeof delta!=="object") return {};

  return Object.fromEntries(
    Object.entries(delta)
      .map(([resource,amount])=>[
        resource,
        Number(amount)||0,
      ])
      .filter(([,amount])=>amount!==0)
  );
}

function resourcePopDeltaForViewer(event){
  const privatePlayerIds=
    Array.isArray(event.privatePlayerIds)
      ?event.privatePlayerIds
      :null;

  if(
    privatePlayerIds &&
    event.publicDelta &&
    typeof event.publicDelta==="object"
  ){
    const viewerId=
      typeof localPlayerId==="function"
        ?localPlayerId()
        :0;

    if(!privatePlayerIds.includes(viewerId)){
      return normalizedResourceDelta(event.publicDelta);
    }
  }

  return normalizedResourceDelta(event.delta);
}

function renderResourcePopEvent(event){
  const layer=$("resourcePopLayer");
  if(!layer || !event) return;

  const delta=resourcePopDeltaForViewer(event);
  const entries=Object.entries(delta);

  if(!entries.length) return;

  const pop=document.createElement("div");
  pop.className="resource-pop";
  pop.dataset.resourcePopEventId=event.id||"";
  pop.style.setProperty(
    "--player-color",
    event.playerColor||"#64748b"
  );

  const detail=entries.map(([resource,amount])=>{
    const icon=RESOURCE_ICON[resource]||"🎴";
    const sign=amount>0?`+${amount}`:`${amount}`;
    const className=
      amount>0
        ?"resource-plus"
        :"resource-minus";

    return `<span class="${className}">${icon}${sign}</span>`;
  }).join("　");

  pop.innerHTML=
    `<div class="resource-pop-title">`+
      `<span>${escapeHtml(event.playerName||"プレイヤー")}</span>`+
      `<span class="resource-pop-reason">`+
        `${escapeHtml(event.reason||"資源変動")}`+
      `</span>`+
    `</div>`+
    `<div class="resource-pop-delta">${detail}</div>`;

  layer.prepend(pop);

  while(layer.children.length>6){
    layer.lastElementChild.remove();
  }

  setTimeout(()=>pop.remove(),2000);
}

function collectResourcePopEvents(){
  if(!game || !Array.isArray(game.resourcePopEvents)) return;

  for(const event of game.resourcePopEvents){
    if(
      !event?.id ||
      shownResourcePopEventIds.has(event.id)
    ){
      continue;
    }

    shownResourcePopEventIds.add(event.id);
    renderResourcePopEvent(event);
  }
}

function showResourceDelta(
  playerId,
  delta,
  reason="資源変動",
  options={}
){
  const normalizedDelta=normalizedResourceDelta(delta);

  if(!Object.keys(normalizedDelta).length || !game) return;

  const player=playerById(playerId);
  if(!player) return;

  if(!Array.isArray(game.resourcePopEvents)){
    game.resourcePopEvents=[];
  }

  const event={
    id:
      `resource-${playerId}-${Date.now()}-`+
      `${Math.random().toString(36).slice(2)}`,
    playerId,
    playerName:player.name,
    playerColor:player.color,
    delta:normalizedDelta,
    reason,
    createdAt:Date.now(),
  };

  if(Array.isArray(options.privatePlayerIds)){
    event.privatePlayerIds=[
      ...new Set(
        options.privatePlayerIds
          .map(Number)
          .filter(Number.isInteger)
      ),
    ];
  }

  if(
    options.publicDelta &&
    typeof options.publicDelta==="object"
  ){
    event.publicDelta=
      normalizedResourceDelta(options.publicDelta);
  }

  game.resourcePopEvents.push(event);
  game.resourcePopEvents=
    game.resourcePopEvents.slice(-48);

  /*
    操作した本人には即時表示。
    他の参加者には次のゲーム状態同期で同じイベントが届く。
  */
  collectResourcePopEvents();
}

function resetPopups(){
  const layer=$("resourcePopLayer");
  if(layer) layer.innerHTML="";
}
function makePlayer(id, human, name=null, clientId=null){
  const names = ["あなた","CPUアオ","CPUキイロ","CPUムラサキ","CPUミドリ","CPUチャ"];
  return {
    id, name:name||names[id], human, clientId, color:PLAYER_COLORS[id],
    resources:{wood:0,brick:0,wool:0,grain:0,ore:0},
    roads:[], settlements:[], cities:[],
    pieces:{road:15,settlement:5,city:4},
    dev:[],
    fishTokens:[],
    fishSwapTurn:-1,
    builtThisTurn:false,
    cpuPlan:null,
    cpuTradeTurnSerial:-1,
    knightsPlayed:0, revealedVP:0, longestRoad:0,
    hasLongestRoad:false, hasLargestArmy:false,
  };
}


function createFishSupply(large){
  return shuffle([
    ...Array(large?15:11).fill(1),
    ...Array(large?15:10).fill(2),
    ...Array(large?13:8).fill(3),
    "boot",
  ]);
}

function newGame(){
  cpuAnalysisAbandonCurrent("new_game");
  cpuStrategicGoalCache.clear();
  cpuRoadSequenceCache.clear();
  clearTimeout(cpuTimer);
  cpuTimer=null;
  cpuActionRunning=false;
  cpuScheduledKey=null;

  clearTimeout(cpuDiscardTimer);
  cpuDiscardTimer=null;
  cpuDiscardScheduledKey=null;
  shownAwardEventIds.clear();
  shownResourcePopEventIds.clear();
  shownTurnAnnouncementEventIds.clear();
  pendingPlacementPreview=null;
  boardPingMode=false;
  boardPingEvents=[];
  clearTimeout(turnAnnouncementTimer);
  turnAnnouncementTimer=null;
  $("turnAnnouncement")?.classList.add("hidden");
  awardDisplayQueue.length=0;
  awardDisplayActive=false;
  clearTimeout(awardDisplayTimer);
  awardDisplayTimer=null;
  $("awardAnnouncement")?.classList.add("hidden");
  clearTimeout(finalResultAutoTimer);
  finalResultAutoTimer=null;
  finalResultWinnerKey=null;
  $("resultModal")?.classList.add("hidden");
  resetPopups();
  hideDiscardModal();
  closeChoiceModal();
  closeTradeModal();
  discardQueue=[];
  discardSelection=null;
  $("log").innerHTML="";
  $("overlayMessage").classList.add("hidden");
  const playerCount=Number($("playerCount").value);
  const large=playerCount>=5;
  const fishermen=$("fishermenEnabled").checked;
  game = {
    playerCount,
    fishermen,
    players:Array.from({length:playerCount},(_,i)=>makePlayer(i,i===0)),
    current:0,
    phase:"setupSettlement",
    setupOrder:[...Array(playerCount).keys(), ...[...Array(playerCount).keys()].reverse()],
    setupIndex:0,
    setupRound:1,
    buildMode:null,
    freeRoads:0,
    rolled:false,
    diceRolling:false,
    diceRollStartedAt:null,
    dice:[0,0],
    turnDice:[0,0],
    diceHistory:[],
    robberHex:null,
    board:createBoard(playerCount,fishermen),
    bank:{wood:large?24:19,brick:large?24:19,wool:large?24:19,grain:large?24:19,ore:large?24:19},
    devDeck:shuffle([
      ...Array(large?20:14).fill("knight"),
      ...Array(5).fill("vp"),
      ...Array(large?3:2).fill("roadBuilding"),
      ...Array(large?3:2).fill("yearOfPlenty"),
      ...Array(large?3:2).fill("monopoly"),
    ]),
    fishSupply:fishermen?createFishSupply(large):[],
    fishDiscard:[],
    oldBootHolder:null,
    selectedFishIndices:[],
    pendingTrade:null,
    resolvedTradeIds:[],
    awardEvents:[],
    resourcePopEvents:[],
    turnAnnouncementEvents:[],
    discardQueue:[],
    discardPlayerId:null,
    pendingFishDraws:[],
    fishSwapPlayerId:null,
    logHistory:[],
    winner:null,
    pendingAfterRobber:null,
    pendingCpuBuildAfterRobber:false,
    turnNo:0,
    turnSerial:1,
  };
  game.robberHex = fishermen ? null : game.board.desertIds[0];
  game.current = game.setupOrder[0];
  render();
  log(`${playerCount}人ゲームを開始しました。初期配置を行います。`);
  if(fishermen) log("漁師拡張：湖・漁場・魚チップ・ボロ靴を使用します。🐱は最初は盤外です。");
  if(large) log("5～6人戦も3～4人戦と同じ通常ターン制で進行します。");
  scheduleCpuIfNeeded();
}

function createBoard(playerCount,fishermen=false){
  const large=playerCount>=5;
  const size=large?60:86;
  const cx=large?511:450;
  const cy=355;
  const axial=[];
  if(large){
    for(let r=-3;r<=3;r++){
      for(let q=-3;q<=2;q++){
        if(-3<=q+r && q+r<=2) axial.push({q,r});
      }
    }
  }else{
    for(let q=-2;q<=2;q++){
      for(let r=-2;r<=2;r++){
        const s=-q-r;
        if(Math.max(Math.abs(q),Math.abs(r),Math.abs(s))<=2) axial.push({q,r});
      }
    }
  }
  axial.sort((a,b)=>(a.r-b.r)||(a.q-b.q));
  const axialSet=new Set(axial.map(axialKey));
  const baseResources=large ? [
    ...Array(6).fill("wood"), ...Array(5).fill("brick"), ...Array(6).fill("wool"),
    ...Array(6).fill("grain"), ...Array(5).fill("ore")
  ] : [
    ...Array(4).fill("wood"), ...Array(3).fill("brick"), ...Array(4).fill("wool"),
    ...Array(4).fill("grain"), ...Array(3).fill("ore")
  ];
  let resources;
  if(fishermen){
    const lakeCount=large?2:1;
    const interior=axial.map((c,i)=>({c,i})).filter(({c})=>{
      let neighbors=0;
      for(const [dq,dr] of HEX_DIRECTIONS){
        if(axialSet.has(`${c.q+dq},${c.r+dr}`)) neighbors++;
      }
      return neighbors===6;
    }).map(x=>x.i);
    const lakeIndexes=shuffle(interior).slice(0,lakeCount);
    const lakeSet=new Set(lakeIndexes);
    const shuffledLand=shuffle(baseResources);
    let ri=0;
    resources=axial.map((_,i)=>lakeSet.has(i)?"lake":shuffledLand[ri++]);
  }else{
    resources=shuffle([...baseResources,...Array(large?2:1).fill("desert")]);
  }

  const cornerHexes=axial.filter(c=>{
    let neighbors=0;
    for(const [dq,dr] of HEX_DIRECTIONS){
      if(axialSet.has(`${c.q+dq},${c.r+dr}`)) neighbors++;
    }
    return neighbors===3;
  });
  const numberStart=cornerHexes[rand(cornerHexes.length)];
  const spiral=createNumberSpiral(axial,numberStart);
  const sequence=large?NUMBER_SEQUENCE_5_6:NUMBER_SEQUENCE_3_4;
  const indexByCoord=new Map(axial.map((c,i)=>[axialKey(c),i]));
  const numbers=Array(axial.length).fill(null);
  let numberIndex=0;
  for(const coord of spiral){
    const boardIndex=indexByCoord.get(axialKey(coord));
    if(["desert","lake"].includes(resources[boardIndex])) continue;
    numbers[boardIndex]=sequence[numberIndex++];
  }
  if(numberIndex!==sequence.length) throw new Error("数値トークンの配置数が一致しません。");

  const lakeNumberSets=fishermen
    ? shuffle(large?[[2,3,11,12],[4,10]]:[[2,3,11,12]])
    : [];
  let lakeNumberIndex=0;
  const vertices={},edges={},hexes=[];
  axial.forEach((a,i)=>{
    const x=cx+size*Math.sqrt(3)*(a.q+a.r/2);
    const y=cy+size*1.5*a.r;
    const corners=[];
    for(let k=0;k<6;k++){
      const ang=Math.PI/180*(60*k-30);
      const px=x+size*Math.cos(ang),py=y+size*Math.sin(ang);
      const pk=keyPoint(px,py);
      if(!vertices[pk]) vertices[pk]={id:pk,x:px,y:py,hexes:[],edges:[],building:null};
      vertices[pk].hexes.push(i);
      corners.push(pk);
    }
    for(let k=0;k<6;k++){
      const a1=corners[k],b1=corners[(k+1)%6],ek=edgeKey(a1,b1);
      if(!edges[ek]) edges[ek]={id:ek,a:a1,b:b1,hexes:[],road:null,harbor:null};
      edges[ek].hexes.push(i);
      if(!vertices[a1].edges.includes(ek)) vertices[a1].edges.push(ek);
      if(!vertices[b1].edges.includes(ek)) vertices[b1].edges.push(ek);
    }
    const lakeNumbers=resources[i]==="lake"?lakeNumberSets[lakeNumberIndex++]:null;
    hexes.push({id:i,q:a.q,r:a.r,x,y,corners,resource:resources[i],number:numbers[i],lakeNumbers});
  });

  const boundary=Object.values(edges).filter(e=>e.hexes.length===1);
  boundary.forEach(e=>{
    const va=vertices[e.a],vb=vertices[e.b];
    e.angle=Math.atan2((va.y+vb.y)/2-cy,(va.x+vb.x)/2-cx);
  });
  boundary.sort((a,b)=>a.angle-b.angle);
  const harborEdgeIndexes=large
    ? [9,13,18,21,24,27,30,33,36,1,6]
    : [7,11,14,17,21,24,27,1,4];
  const chosen=harborEdgeIndexes.map(i=>boundary[i]);
  const harborTypes=large
    ? ["wool","3:1","3:1","brick","wool","wood","3:1","grain","3:1","ore","3:1"]
    : ["wool","3:1","3:1","brick","wood","3:1","grain","ore","3:1"];
  chosen.forEach((e,i)=>e.harbor=harborTypes[i]);

  let fishingGrounds=[];
  if(fishermen){
    const boundaryIds=new Set(boundary.map(e=>e.id));
    const candidates=Object.values(vertices).filter(v=>{
      const coastEdges=v.edges.filter(eid=>boundaryIds.has(eid));
      return v.hexes.length===2 && coastEdges.length===2 &&
        coastEdges.every(eid=>!edges[eid].harbor);
    }).sort((a,b)=>Math.atan2(a.y-cy,a.x-cx)-Math.atan2(b.y-cy,b.x-cx));
    const expected=large?8:6;
    if(candidates.length!==expected){
      throw new Error(`漁場位置が${candidates.length}か所です（必要数${expected}）。港配置を確認してください。`);
    }
    const fishingNumbers=shuffle(large?[4,5,5,6,8,9,9,10]:[4,5,6,8,9,10]);
    fishingGrounds=candidates.map((v,i)=>({id:i,vertexId:v.id,number:fishingNumbers[i]}));
  }
  const deserts=hexes.filter(h=>h.resource==="desert").map(h=>h.id);
  const lakes=hexes.filter(h=>h.resource==="lake").map(h=>h.id);
  return {size,cx,cy,hexes,vertices,edges,harbors:chosen.map(e=>e.id),desertIds:deserts,lakeIds:lakes,fishingGrounds,large,numberStart:axialKey(numberStart)};
}

function currentPlayer(){ return game.players[game.current]; }
function playerById(id){ return game.players[id]; }
function totalResources(p){ return RESOURCES.reduce((s,r)=>s+p.resources[r],0); }

function expectedResourceSupply(){
  return game?.playerCount>=5 ? 24 : 19;
}

function enforceResourceIntegrity(){
  if(!game?.players || !game?.bank) return false;

  let changed=false;
  const expected=expectedResourceSupply();

  for(const player of game.players){
    if(!player.resources){
      player.resources=Object.fromEntries(
        RESOURCES.map(resource=>[resource,0])
      );
      changed=true;
    }

    for(const resource of RESOURCES){
      const raw=Number(player.resources[resource]);
      const normalized=Number.isFinite(raw)
        ?Math.max(0,Math.floor(raw))
        :0;

      if(raw!==normalized){
        player.resources[resource]=normalized;
        changed=true;
      }
    }
  }

  for(const resource of RESOURCES){
    const playersTotal=game.players.reduce(
      (sum,player)=>sum+player.resources[resource],
      0
    );
    const correctedBank=Math.max(0,expected-playersTotal);

    if(game.bank[resource]!==correctedBank){
      game.bank[resource]=correctedBank;
      changed=true;
    }
  }

  return changed;
}

function normalizedTradeAmount(value){
  const amount=Number(value);
  if(!Number.isInteger(amount) || amount<0) return null;
  return amount;
}

function isTradeBundleValid(bundle){
  if(!bundle || typeof bundle!=="object") return false;

  return RESOURCES.every(resource=>{
    const amount=normalizedTradeAmount(bundle[resource]||0);
    return amount!==null && amount<=TRADE_REQUEST_MAX;
  });
}

function canExecutePlayerTrade(player,target,give,get){
  if(!player || !target || player.id===target.id) return false;
  if(!isTradeBundleValid(give) || !isTradeBundleValid(get)) return false;

  const giveTotal=RESOURCES.reduce(
    (sum,resource)=>sum+(give[resource]||0),
    0
  );
  const getTotal=RESOURCES.reduce(
    (sum,resource)=>sum+(get[resource]||0),
    0
  );

  if(giveTotal<=0 || getTotal<=0) return false;

  for(const resource of RESOURCES){
    const offered=give[resource]||0;
    const requested=get[resource]||0;

    if(offered>0 && requested>0) return false;
    if(offered>player.resources[resource]) return false;
    if(requested>target.resources[resource]) return false;
  }

  return true;
}

function tradeWasResolved(tradeId){
  if(!tradeId) return false;

  return locallyResolvedTradeIds.has(tradeId) ||
    !!game?.resolvedTradeIds?.includes(tradeId);
}

function rememberResolvedTrade(tradeId){
  if(!tradeId) return;

  locallyResolvedTradeIds.add(tradeId);

  if(!Array.isArray(game.resolvedTradeIds)){
    game.resolvedTradeIds=[];
  }

  if(!game.resolvedTradeIds.includes(tradeId)){
    game.resolvedTradeIds.push(tradeId);
    game.resolvedTradeIds=game.resolvedTradeIds.slice(-50);
  }
}
function hasCost(p,cost){ return Object.entries(cost).every(([r,n])=>p.resources[r]>=n); }

function missingCostItems(player,cost){
  return Object.entries(cost)
    .map(([resource,needed])=>({
      resource,
      needed,
      owned:Math.max(0,player.resources[resource]||0),
    }))
    .filter(item=>item.owned<item.needed);
}

function missingCostText(player,cost){
  const missing=missingCostItems(player,cost);
  if(!missing.length) return "";
  return missing
    .map(item=>
      `${RESOURCE_JA[item.resource]}があと${item.needed-item.owned}枚`
    )
    .join("、");
}

function grantFreeDevelopmentCard(player,reason="無料発展カード"){
  if(!game.devDeck.length) return false;

  // 無料取得の前後で通常建設回数を必ず維持する。
  const builtStateBefore=player.builtThisTurn;
  const card=game.devDeck.pop();
  player.dev.push(card);
  player.builtThisTurn=builtStateBefore;
  queueAwardEvent("devDraw",player.id);

  log(`${reason}で発展カードを1枚引きました（通常建設回数は消費しません）。`);
  return true;
}
function payCost(p,cost,reason="支払い"){
  const delta={};
  for(const [r,n] of Object.entries(cost)){
    p.resources[r]-=n; game.bank[r]+=n; delta[r]=-n;
  }
  showResourceDelta(p.id,delta,reason);
}
function gainResource(p,r,n=1){
  const amount=Math.min(n,game.bank[r]);
  p.resources[r]+=amount; game.bank[r]-=amount;
  return amount;
}
function vertexNeighbors(vertexId){
  const v=game.board.vertices[vertexId];
  return v.edges.map(eid=>{
    const e=game.board.edges[eid];
    return e.a===vertexId?e.b:e.a;
  });
}
function canPlaceSettlement(playerId, vertexId, setup=false){
  const v=game.board.vertices[vertexId];
  if(!v || v.building) return false;
  if(vertexNeighbors(vertexId).some(n=>game.board.vertices[n].building)) return false;
  if(setup) return true;
  return v.edges.some(eid=>game.board.edges[eid].road===playerId);
}
function canPlaceRoad(playerId, edgeId, setupVertex=null){
  const e=game.board.edges[edgeId];
  if(!e || e.road!==null) return false;
  if(setupVertex && e.a!==setupVertex && e.b!==setupVertex) return false;
  for(const vid of [e.a,e.b]){
    const b=game.board.vertices[vid].building;
    if(b && b.player===playerId) return true;
    if(b && b.player!==playerId) continue;
    if(game.board.vertices[vid].edges.some(other=>game.board.edges[other].road===playerId)) return true;
  }
  return false;
}
function canUpgradeCity(playerId,vertexId){
  const b=game.board.vertices[vertexId]?.building;
  return b && b.player===playerId && b.type==="settlement";
}


function isFishingVertex(vertexId){
  if(!game.fishermen) return false;
  if(game.board.fishingGrounds.some(f=>f.vertexId===vertexId)) return true;
  return game.board.vertices[vertexId].hexes.some(hid=>game.board.hexes[hid].resource==="lake");
}

function placeSettlement(playerId,vertexId,setup=false){
  const p=playerById(playerId);
  game.board.vertices[vertexId].building={player:playerId,type:"settlement"};
  p.settlements.push(vertexId); p.pieces.settlement--;
  if(setup && game.setupRound===2){
    const delta={};
    for(const hid of game.board.vertices[vertexId].hexes){
      const r=game.board.hexes[hid].resource;
      if(RESOURCES.includes(r)){
        const got=gainResource(p,r,1);
        if(got) delta[r]=(delta[r]||0)+got;
      }
    }
    showResourceDelta(p.id,delta,"初期資源");
    if(game.fishermen && isFishingVertex(vertexId)){
      drawFishTokensForPlayer(p.id,1,"初期漁獲");
    }
  }
}

function placeRoad(playerId,edgeId,free=false){
  const p=playerById(playerId);
  game.board.edges[edgeId].road=playerId;
  p.roads.push(edgeId); p.pieces.road--;
  if(!free) payCost(p,COST.road,"街道建設");
  updateAwards();
}

function placeCity(playerId,vertexId){
  const p=playerById(playerId);
  game.board.vertices[vertexId].building.type="city";
  p.settlements=p.settlements.filter(v=>v!==vertexId);
  p.cities.push(vertexId); p.pieces.city--; p.pieces.settlement++;
  payCost(p,COST.city,"都市建設");
}

function buyDev(playerId){
  const p=playerById(playerId);
  if(!p || !game.devDeck.length || !hasCost(p,COST.dev)) return false;
  payCost(p,COST.dev,"発展カード");
  const card=game.devDeck.pop();
  p.dev.push(card);
  p.builtThisTurn=true;
  queueAwardEvent("devDraw",p.id);
  log(`${p.name}が発展カードを1枚購入しました。`);
  return true;
}
function setupClickVertex(vertexId){
  const p=currentPlayer();

  if(
    game.phase!=="setupSettlement" ||
    !isLocalPlayer(p)
  ){
    return;
  }

  if(!canPlaceSettlement(p.id,vertexId,true)){
    log("そこには開拓地を置けません。");
    return;
  }

  requestPlacementConfirmation({
    kind:"settlement",
    targetId:vertexId,
    itemName:"開拓地",
    guide:"初期開拓地をこの交差点に置きます。",
    onConfirm:()=>{
      const player=currentPlayer();

      if(
        game.phase!=="setupSettlement" ||
        !isLocalPlayer(player) ||
        !canPlaceSettlement(
          player.id,
          vertexId,
          true
        )
      ){
        log("その場所には置けなくなりました。");
        render();
        return;
      }

      cpuAnalysisQueueHumanReceipt(
        player,
        "setup_settlement",
        {vertexId}
      );

      placeSettlement(
        player.id,
        vertexId,
        true
      );
      game.setupVertex=vertexId;
      game.phase="setupRoad";

      log(
        `${player.name}が初期開拓地を置きました。`+
        "隣接する辺に街道を置いてください。"
      );
      render();
    },
  });
}
function setupClickEdge(edgeId){
  const p=currentPlayer();

  if(
    game.phase!=="setupRoad" ||
    !isLocalPlayer(p)
  ){
    return;
  }

  if(
    !canPlaceRoad(
      p.id,
      edgeId,
      game.setupVertex
    )
  ){
    log("初期開拓地に接する辺を選んでください。");
    return;
  }

  requestPlacementConfirmation({
    kind:"road",
    targetId:edgeId,
    itemName:"街道",
    guide:"初期街道をこの辺に置きます。",
    onConfirm:()=>{
      const player=currentPlayer();

      if(
        game.phase!=="setupRoad" ||
        !isLocalPlayer(player) ||
        !canPlaceRoad(
          player.id,
          edgeId,
          game.setupVertex
        )
      ){
        log("その場所には置けなくなりました。");
        render();
        return;
      }

      cpuAnalysisQueueHumanReceipt(
        player,
        "setup_road",
        {edgeId}
      );

      game.board.edges[edgeId].road=player.id;
      player.roads.push(edgeId);
      player.pieces.road--;

      log(`${player.name}が初期街道を置きました。`);
      advanceSetup();
    },
  });
}

function advanceSetup(){
  game.setupIndex++;
  if(game.setupIndex>=game.setupOrder.length){
    game.current=0;
    game.phase="turn";
    game.rolled=false;
    game.turnNo=1;
    cpuActionRunning=false;
    clearTimeout(cpuTimer);
    cpuTimer=null;
    cpuScheduledKey=null;
    log("初期配置が完了しました。ゲームを開始します。");
    queueTurnAnnouncement(game.current);
    render();
    scheduleCpuIfNeeded();
    return;
  }
  game.current=game.setupOrder[game.setupIndex];
  game.setupRound=game.setupIndex<game.playerCount?1:2;
  game.phase="setupSettlement";
  game.setupVertex=null;

  if(currentPlayer().human){
    cpuActionRunning=false;
    clearTimeout(cpuTimer);
    cpuTimer=null;
    cpuScheduledKey=null;
    if(isLocalPlayer(currentPlayer())){
      log(`あなたの初期配置 ${game.setupRound}/2 です。開拓地を置いてください。`);
    }
  }

  render();
  scheduleCpuIfNeeded();
}


function recordDiceResult(playerId,dice){
  if(!game || !Array.isArray(dice) || dice.length<2) return;

  if(!Array.isArray(game.diceHistory)){
    game.diceHistory=[];
  }

  const eventId=`${game.turnSerial}:${playerId}`;

  if(game.diceHistory.some(event=>event.id===eventId)){
    return;
  }

  const player=playerById(playerId);
  const normalizedDice=[
    Math.max(1,Math.min(6,Number(dice[0])||1)),
    Math.max(1,Math.min(6,Number(dice[1])||1)),
  ];

  game.diceHistory.push({
    id:eventId,
    turnSerial:game.turnSerial,
    turnNo:game.turnNo,
    playerId,
    playerName:player?.name||`プレイヤー${playerId+1}`,
    dice:normalizedDice,
    sum:normalizedDice[0]+normalizedDice[1],
  });

  game.diceHistory=game.diceHistory.slice(-500);
}

function diceResultCounts(){
  const counts=Object.fromEntries(
    Array.from({length:11},(_,index)=>[index+2,0])
  );

  for(const event of game?.diceHistory||[]){
    if(counts[event.sum]!==undefined){
      counts[event.sum]++;
    }
  }

  return counts;
}

function resultDiceHtml(){
  const history=game?.diceHistory||[];
  const counts=diceResultCounts();
  const total=history.length;
  const maximum=Math.max(1,...Object.values(counts));

  const distribution=Object.entries(counts).map(([sum,count])=>{
    const width=(count/maximum)*100;
    const rate=total?Math.round((count/total)*100):0;

    return `<div class="dice-result-row">
      <span class="dice-result-sum">${sum}</span>
      <div class="dice-result-track">
        <span class="dice-result-bar" style="width:${width}%"></span>
      </div>
      <b>${count}回</b>
      <small>${rate}%</small>
    </div>`;
  }).join("");

  const recent=history.length
    ?history.slice(-24).reverse().map(event=>
      `<span class="dice-history-chip" title="${event.playerName}">
        <span>${event.dice[0]}</span>
        <span>${event.dice[1]}</span>
        <b>${event.sum}</b>
      </span>`
    ).join("")
    :'<p class="result-empty">まだダイスは振られていません。</p>';

  return `<section class="result-section">
    <div class="result-section-heading">
      <h3>ダイスの出目</h3>
      <span>合計 ${total}回</span>
    </div>
    <div class="dice-result-list">${distribution}</div>
    <h4>直近の出目</h4>
    <div class="dice-history-list">${recent}</div>
  </section>`;
}

function finalPlayerResultHtml(){
  const ranking=[...game.players].sort((a,b)=>{
    const pointDifference=totalVP(b)-totalVP(a);
    if(pointDifference) return pointDifference;

    const publicDifference=visibleVP(b)-visibleVP(a);
    if(publicDifference) return publicDifference;

    return a.id-b.id;
  });

  return `<section class="result-section">
    <div class="result-section-heading">
      <h3>最終順位</h3>
      <span>${game.turnNo}ラウンド</span>
    </div>
    <div class="final-ranking">
      ${ranking.map((player,index)=>{
        const awards=[
          player.hasLongestRoad?"最長交易路":"",
          player.hasLargestArmy?"最大騎士団":"",
          game.fishermen&&game.oldBootHolder===player.id?"ボロ靴":"",
        ].filter(Boolean);

        return `<article class="final-player-result ${player.id===game.winner?"winner":""}">
          <span class="final-rank">${index+1}</span>
          <span class="player-dot" style="background:${player.color}"></span>
          <div class="final-player-main">
            <div class="final-player-name">
              ${player.name}
              ${player.id===game.winner?'<strong>勝者</strong>':""}
            </div>
            <div class="final-player-stats">
              <span>街道 ${player.roads.length}</span>
              <span>最長 ${player.longestRoad}</span>
              <span>開拓地 ${player.settlements.length}</span>
              <span>都市 ${player.cities.length}</span>
              <span>騎士 ${player.knightsPlayed}</span>
              <span>資源 ${totalResources(player)}</span>
              <span>発展 ${player.dev.length}</span>
              ${game.fishermen?`<span>魚 ${player.fishTokens.length}枚・${fishTotal(player)}匹</span>`:""}
            </div>
            ${awards.length
              ?`<div class="final-player-awards">${awards.map(award=>`<span>${award}</span>`).join("")}</div>`
              :""
            }
          </div>
          <b class="final-player-points">${totalVP(player)}点</b>
        </article>`;
      }).join("")}
    </div>
  </section>`;
}

function closeResultModal(){
  $("resultModal")?.classList.add("hidden");
}

function openResultModal(){
  if(!game) return;

  const finished=game.winner!==null;
  $("resultTitle").textContent=finished
    ?"ゲームリザルト"
    :"途中経過";
  $("resultGuide").textContent=finished
    ?"全プレイヤーの最終結果と、ゲーム全体のダイス出目を表示します。"
    :"ゲーム中はダイスの出目だけ表示します。順位や得点はゲーム終了まで非表示です。";

  $("resultContent").innerHTML=
    (finished?finalPlayerResultHtml():"")+
    resultDiceHtml();

  $("resultModal").classList.remove("hidden");
}

function scheduleFinalResultIfNeeded(){
  if(!game || game.winner===null){
    clearTimeout(finalResultAutoTimer);
    finalResultAutoTimer=null;
    finalResultWinnerKey=null;
    return;
  }

  const winnerKey=`${game.winner}:${game.turnSerial}`;

  if(finalResultWinnerKey===winnerKey){
    return;
  }

  finalResultWinnerKey=winnerKey;
  clearTimeout(finalResultAutoTimer);

  finalResultAutoTimer=setTimeout(()=>{
    if(game?.winner!==null){
      openResultModal();
    }
  },2400);
}

function rollDice(){
  if(game.winner || game.phase!=="turn" || !isLocalTurn() || game.rolled || game.diceRolling) return;
  const player=currentPlayer();
  cpuAnalysisQueueHumanReceipt(player,"roll_dice",{});
  animateDiceRoll(player.id,()=>{});
}

function animateDiceRoll(playerId,afterResolve){
  if(game.diceRolling) return;

  const startedAt=Date.now();
  const rollDurationMs=760;

  game.diceRolling=true;
  game.diceRollStartedAt=startedAt;

  const d1=$("die1"), d2=$("die2");
  d1.classList.add("rolling");
  d2.classList.add("rolling");
  render();

  let ticks=0;
  let finished=false;

  const finishRoll=()=>{
    if(finished) return;
    finished=true;
    clearInterval(interval);

    d1.classList.remove("rolling");
    d2.classList.remove("rolling");

    game.diceRolling=false;
    game.diceRollStartedAt=null;

    const finalDice=[1+rand(6),1+rand(6)];
    resolveDiceRoll(
      playerId,
      finalDice,
      afterResolve
    );
  };

  const interval=setInterval(()=>{
    game.dice=[1+rand(6),1+rand(6)];
    d1.textContent=game.dice[0];
    d2.textContent=game.dice[1];
    ticks++;

    /*
      背景タブなどでsetIntervalが間引かれても、
      回数ではなく実時間でも終了判定する。
    */
    if(
      ticks>=11 ||
      Date.now()-startedAt>=rollDurationMs
    ){
      finishRoll();
    }
  },65);
}

function resolveDiceRoll(playerId,dice,afterResolve){
  /*
    どの経路から呼ばれてもロール中フラグを残さない。
  */
  game.diceRolling=false;
  game.diceRollStartedAt=null;
  game.dice=[...dice];
  game.turnDice=[...dice];
  game.rolled=true;
  recordDiceResult(playerId,dice);
  const p=playerById(playerId);
  const sum=dice[0]+dice[1];
  log(`${p.name}が ${sum} を出しました。`);
  if(sum===7){
    cpuAnalysisRecordAction(p,"dice_roll",{dice:[...dice],sum,seven:true});
    queueAwardEvent("robberAppears");
    handleSeven(playerId,afterResolve);
    render();
    return;
  }
  produce(sum);
  cpuAnalysisRecordAction(p,"dice_roll",{dice:[...dice],sum,seven:false});
  render();
  if(typeof afterResolve==="function" && game.phase==="turn" && !game.winner){
    const delay=p?.human ?280:CPU_ACTION_DELAY_MS;
    setTimeout(afterResolve,delay);
  }
}

function produce(sum){
  const demand=Object.fromEntries(RESOURCES.map(r=>[r,game.players.map(()=>0)]));
  for(const h of game.board.hexes){
    if(h.number!==sum || game.robberHex===h.id || h.resource==="desert") continue;
    for(const vid of h.corners){
      const b=game.board.vertices[vid].building;
      if(b) demand[h.resource][b.player]+=b.type==="city"?2:1;
    }
  }
  const gains=game.players.map(()=>({}));
  for(const r of RESOURCES){
    const claims=demand[r];
    const total=claims.reduce((a,b)=>a+b,0);
    if(total===0) continue;
    const receivingPlayers=claims.filter(n=>n>0).length;
    if(game.bank[r]>=total){
      claims.forEach((n,pid)=>{
        if(!n) return;
        const got=gainResource(playerById(pid),r,n);
        if(got) gains[pid][r]=(gains[pid][r]||0)+got;
      });
    }else if(receivingPlayers===1){
      const pid=claims.findIndex(n=>n>0);
      const got=gainResource(playerById(pid),r,claims[pid]);
      if(got) gains[pid][r]=(gains[pid][r]||0)+got;
    }else{
      log(`銀行の${RESOURCE_JA[r]}が不足したため、この資源は誰も受け取れませんでした。`);
    }
  }
  gains.forEach((delta,i)=>{
    const text=Object.entries(delta).map(([r,n])=>`${RESOURCE_JA[r]}${n}`).join("、");
    if(text){
      log(`${playerById(i).name}：${text}を獲得。`);
      showResourceDelta(i,delta,`出目 ${sum}`);
    }
  });
  if(game.fishermen) produceFish(sum);
}

function replenishFishSupply(){
  if(game.fishSupply.length || !game.fishDiscard.length) return;
  game.fishSupply=shuffle(game.fishDiscard);
  game.fishDiscard=[];
  log("魚チップの捨て山を混ぜ、新しい山札にしました。");
}

function drawRawFishToken(){
  replenishFishSupply();
  return game.fishSupply.length?game.fishSupply.pop():null;
}

function receiveFishToken(player,token,reason){
  if(token==="boot"){
    game.oldBootHolder=player.id;
    queueAwardEvent("oldBoot",player.id);
    log(`${player.name}がボロ靴を引き、即座に公開しました。勝利に必要な点数が1点増えます。`);
  }else{
    player.fishTokens.push(token);
    const detail=isLocalPlayer(player)?`（${token}匹）`:"";
    log(`${player.name}が魚チップを1枚獲得しました${detail}。`);
  }
  if(isLocalPlayer(player)) game.selectedFishIndices=[];
}

function chooseFishSwapIndex(player){
  if(player.fishSwapTurn===game.turnSerial) return null;
  player.fishSwapTurn=game.turnSerial;
  if(isLocalPlayer(player)){
    const tokenOptions=player.fishTokens.map((value,index)=>({
      value:index,
      label:`魚${value}匹`,
      icon:"🐟",
      sub:"このチップを捨てて1枚引き直す",
    }));
    openChoiceModal({
      title:"魚チップが7枚あります",
      guide:"捨てる魚チップをクリックしてください。引き直した後、この出目での魚獲得は終了します。",
      options:[
        ...tokenOptions,
        {value:null,label:"引き直さない",icon:"×",sub:"今回は魚チップを受け取らない",className:"no"},
      ],
      allowCancel:false,
      onSelect:index=>{
        if(index===null){
          log(`${player.name}は魚チップの引き直しを行いませんでした。`);
          renderSide();
          return;
        }
        const [discarded]=player.fishTokens.splice(index,1);
        game.fishDiscard.push(discarded);
        log(`${player.name}が魚${discarded}匹のチップを捨てて引き直します。`);
        const replacement=drawRawFishToken();
        if(replacement!==null) receiveFishToken(player,replacement,"引き直し");
        renderSide();
      },
    });
    return null;
  }
  const min=Math.min(...player.fishTokens);
  if(min>=3) return null;
  return player.fishTokens.indexOf(min);
}

function drawFishTokensForPlayer(playerId,count,reason="漁獲"){
  if(!game.fishermen || count<=0) return;
  const player=playerById(playerId);
  let drawn=0;
  for(let i=0;i<count;i++){
    if(player.fishTokens.length>=7){
      const swapIndex=chooseFishSwapIndex(player);
      if(swapIndex===null) break;
      const [discarded]=player.fishTokens.splice(swapIndex,1);
      game.fishDiscard.push(discarded);
      log(`${player.name}が魚チップ1枚を捨てて引き直します。`);
      const replacement=drawRawFishToken();
      if(replacement!==null){ receiveFishToken(player,replacement,reason); drawn++; }
      break;
    }
    const token=drawRawFishToken();
    if(token===null){ log("魚チップの山札が空で、受け取れませんでした。"); break; }
    receiveFishToken(player,token,reason);
    drawn++;
  }
  if(drawn) renderSide();
}

function openPendingFishSwapModal(player){
  const key=`${game.turnSerial}:${player.id}:${game.pendingFishDraws?.[0]?.remaining||0}`;
  if(shownFishSwapKey===key) return;
  shownFishSwapKey=key;
  const tokenOptions=player.fishTokens.map((value,index)=>({
    value:index,
    label:`魚${value}匹`,
    icon:"🐟",
    sub:"このチップを捨てて1枚引き直す",
  }));
  openChoiceModal({
    title:"魚チップが7枚あります",
    guide:"捨てる魚チップをクリックしてください。引き直した後、この出目での魚獲得は終了します。",
    options:[
      ...tokenOptions,
      {value:null,label:"引き直さない",icon:"×",sub:"今回は魚チップを受け取らない",className:"no"},
    ],
    allowCancel:false,
    onSelect:index=>{
      shownFishSwapKey=null;
      const current=game.pendingFishDraws?.[0];
      if(!current || current.playerId!==player.id) return;
      if(index===null){
        log(`${player.name}は魚チップの引き直しを行いませんでした。`);
      }else{
        const [discarded]=player.fishTokens.splice(index,1);
        game.fishDiscard.push(discarded);
        log(`${player.name}が魚${discarded}匹のチップを捨てて引き直します。`);
        const replacement=drawRawFishToken();
        if(replacement!==null) receiveFishToken(player,replacement,"引き直し");
      }
      game.pendingFishDraws.shift();
      game.fishSwapPlayerId=null;
      processFishDrawQueue();
    },
  });
}

function processFishDrawQueue(){
  if(!Array.isArray(game.pendingFishDraws)) game.pendingFishDraws=[];
  while(game.pendingFishDraws.length){
    const item=game.pendingFishDraws[0];
    const player=playerById(item.playerId);
    if(!player || item.remaining<=0){
      game.pendingFishDraws.shift();
      continue;
    }

    if(player.fishTokens.length<7){
      const token=drawRawFishToken();
      if(token===null){
        log("魚チップの山札が空で、受け取れませんでした。");
        game.pendingFishDraws.shift();
        continue;
      }
      receiveFishToken(player,token,item.reason);
      item.remaining--;
      continue;
    }

    if(player.fishSwapTurn===game.turnSerial){
      game.pendingFishDraws.shift();
      continue;
    }

    player.fishSwapTurn=game.turnSerial;
    game.phase="fishSwap";
    game.fishSwapPlayerId=player.id;
    render();

    if(!player.human){
      if(ONLINE_MODE && !isOnlineHost()) return;
      const min=Math.min(...player.fishTokens);
      if(min<3){
        const index=player.fishTokens.indexOf(min);
        const [discarded]=player.fishTokens.splice(index,1);
        game.fishDiscard.push(discarded);
        const replacement=drawRawFishToken();
        if(replacement!==null) receiveFishToken(player,replacement,"引き直し");
      }
      game.pendingFishDraws.shift();
      game.fishSwapPlayerId=null;
      continue;
    }

    if(isLocalPlayer(player)) openPendingFishSwapModal(player);
    return;
  }

  game.fishSwapPlayerId=null;
  if(game.phase==="fishSwap") game.phase="turn";
  render();

  /*
    v1.54:
    CPUのダイス結果で人間の魚7枚処理へ一時停止した場合、
    人間側の魚交換が終わった直後にCPU進行を再評価する。
    scheduleCpuIfNeeded側は「ダイス済みCPU」を再ロールさせず、
    ダイス後処理から復帰する。
  */
  if(typeof scheduleCpuIfNeeded==="function"){
    scheduleCpuIfNeeded();
  }
}

function produceFish(sum){
  const claims=game.players.map(()=>0);
  for(const ground of game.board.fishingGrounds){
    if(ground.number!==sum) continue;
    const b=game.board.vertices[ground.vertexId].building;
    if(b) claims[b.player]+=b.type==="city"?2:1;
  }
  for(const h of game.board.hexes){
    if(h.resource!=="lake" || game.robberHex===h.id || !h.lakeNumbers.includes(sum)) continue;
    for(const vid of h.corners){
      const b=game.board.vertices[vid].building;
      if(b) claims[b.player]+=b.type==="city"?2:1;
    }
  }

  game.pendingFishDraws=[];
  for(let offset=0;offset<game.playerCount;offset++){
    const pid=(game.current+offset)%game.playerCount;
    if(claims[pid]){
      game.pendingFishDraws.push({
        playerId:pid,
        remaining:claims[pid],
        reason:`出目 ${sum}`,
      });
    }
  }
  processFishDrawQueue();
}

function hideDiscardModal(){
  const modal=$("discardModal");
  if(modal) modal.classList.add("hidden");
}

function cpuStableTie(value){
  const text=String(value??"");
  let hash=2166136261;

  for(let i=0;i<text.length;i++){
    hash^=text.charCodeAt(i);
    hash=Math.imul(hash,16777619);
  }

  return ((hash>>>0)%1000)/1000;
}

function cpuBuildingMultiplier(building){
  return building?.type==="city" ? 2 : 1;
}

function cpuResourceProduction(player,resource){
  if(!player || !game?.board) return 0;

  let score=0;

  const vertices=[
    ...player.settlements,
    ...player.cities,
  ];

  for(const vertexId of vertices){
    const building=
      game.board.vertices[vertexId]?.building;

    const multiplier=
      cpuBuildingMultiplier(building);

    for(const hexId of game.board.vertices[vertexId]?.hexes||[]){
      const hex=game.board.hexes[hexId];

      if(
        !hex ||
        hex.resource!==resource
      ){
        continue;
      }

      if(hex.number){
        const robberFactor=
          game.robberHex===hexId
            ?0.22
            :1;

        score +=
          (PIPS[hex.number]||0)*
          multiplier*
          robberFactor;
      }
    }
  }

  return score;
}

function cpuProductionResources(player){
  const result={};

  for(const resource of RESOURCES){
    result[resource]=
      cpuResourceProduction(
        player,
        resource
      );
  }

  return result;
}

function cpuVertexHarborBonus(vertexId,playerId){
  const vertex=game.board.vertices[vertexId];
  if(!vertex) return 0;

  const player=playerById(playerId);
  const production=
    player
      ?cpuProductionResources(player)
      :Object.fromEntries(
        RESOURCES.map(resource=>[resource,0])
      );

  let best=0;

  for(const edgeId of vertex.edges){
    const harbor=
      game.board.edges[edgeId]?.harbor;

    if(!harbor) continue;

    if(harbor==="3:1"){
      best=Math.max(best,1.8);
      continue;
    }

    const matchingProduction=
      production[harbor]||0;

    best=Math.max(
      best,
      2.4+
      Math.min(2.4,matchingProduction*.35)
    );
  }

  return best;
}

function cpuVertexStrategicScore(
  vertexId,
  playerId,
  options={}
){
  const vertex=
    game.board.vertices[vertexId];

  if(!vertex) return -9999;

  const player=playerById(playerId);
  const setup=!!options.setup;

  let score=0;
  const resourceSet=new Set();
  const numberSet=new Set();

  const existingProduction=
    player
      ?cpuProductionResources(player)
      :Object.fromEntries(
        RESOURCES.map(resource=>[resource,0])
      );

  const resourceWeights={
    wood:1.08,
    brick:1.12,
    wool:.96,
    grain:1.18,
    ore:1.16,
  };

  for(const hexId of vertex.hexes){
    const hex=game.board.hexes[hexId];
    if(!hex) continue;

    let pips=0;

    if(hex.number){
      pips=PIPS[hex.number]||0;
      numberSet.add(hex.number);
    }else if(
      hex.resource==="lake" &&
      Array.isArray(hex.lakeNumbers)
    ){
      pips=
        hex.lakeNumbers.reduce(
          (sum,number)=>
            sum+(PIPS[number]||0),
          0
        )*.42;
    }

    if(RESOURCES.includes(hex.resource)){
      const resource=hex.resource;
      resourceSet.add(resource);

      score +=
        pips*
        resourceWeights[resource];

      if(
        player &&
        existingProduction[resource]<=0
      ){
        score +=
          setup &&
          player.settlements.length>=1
            ?3.4
            :2.1;
      }

      if(
        setup &&
        player?.settlements.length===0 &&
        (
          resource==="wood" ||
          resource==="brick" ||
          resource==="grain"
        )
      ){
        score += .8;
      }
    }else{
      score += pips*.6;
    }
  }

  score += resourceSet.size*2.25;
  score += numberSet.size*.55;

  if(
    setup &&
    player &&
    player.settlements.length>=1
  ){
    const production=
      cpuProductionResources(player);

    for(const resource of RESOURCES){
      if(
        resourceSet.has(resource) &&
        (production[resource]||0)<=0
      ){
        score+=4.1;
      }
    }

    /*
      2軒の初期配置で同じ数字へ偏りすぎるのを抑える。
      片方が止まっても全生産が止まりにくくする。
    */
    const existingNumbers=new Set();

    for(const settlementId of player.settlements){
      for(
        const hexId of
        game.board.vertices[
          settlementId
        ]?.hexes||[]
      ){
        const number=
          game.board.hexes[
            hexId
          ]?.number;

        if(number){
          existingNumbers.add(number);
        }
      }
    }

    for(const number of numberSet){
      if(existingNumbers.has(number)){
        score-=1.15;
      }
    }
  }
  score += cpuVertexHarborBonus(
    vertexId,
    playerId
  );

  if(
    game.fishermen &&
    isFishingVertex(vertexId)
  ){
    score += 2.4;
  }

  /*
    同点付近だけわずかな揺らぎを持たせ、
    毎回完全に同じ初期配置にはしない。
  */
  score += cpuStableTie(`vertex:${vertexId}`)*.035;

  return score;
}

function cpuStrategyProfile(player){
  const production=
    cpuProductionResources(player);

  const expandPower=
    (production.wood||0)+
    (production.brick||0)+
    (production.wool||0)*.65+
    (production.grain||0)*.8;

  const cityPower=
    (production.ore||0)*1.28+
    (production.grain||0)*1.12;

  if(
    cityPower>=expandPower*1.18 &&
    (production.ore||0)>=4
  ){
    return "city";
  }

  if(
    expandPower>=cityPower*1.12
  ){
    return "expand";
  }

  return "balanced";
}

function cpuNetworkVertices(player){
  const vertices=new Set([
    ...player.settlements,
    ...player.cities,
  ]);

  for(const edgeId of player.roads){
    const edge=game.board.edges[edgeId];
    if(!edge) continue;

    vertices.add(edge.a);
    vertices.add(edge.b);
  }

  return [...vertices];
}

function cpuExpansionPathToVertex(
  player,
  targetId,
  maxRoads=5
){
  const starts=
    cpuNetworkVertices(player);

  if(!starts.length) return null;

  const bestCost=new Map();
  const queue=[];

  for(const startId of starts){
    bestCost.set(startId,0);
    queue.push({
      vertexId:startId,
      cost:0,
      roadPath:[],
    });
  }

  while(queue.length){
    queue.sort(
      (a,b)=>a.cost-b.cost
    );

    const current=queue.shift();

    if(
      current.cost>
      (bestCost.get(current.vertexId)??Infinity)
    ){
      continue;
    }

    if(current.vertexId===targetId){
      return current.roadPath;
    }

    const vertex=
      game.board.vertices[
        current.vertexId
      ];

    if(!vertex) continue;

    const blockingBuilding=
      vertex.building &&
      vertex.building.player!==player.id;

    if(
      blockingBuilding &&
      current.vertexId!==targetId
    ){
      continue;
    }

    for(const edgeId of vertex.edges){
      const edge=
        game.board.edges[edgeId];

      if(!edge) continue;

      if(
        edge.road!==null &&
        edge.road!==player.id
      ){
        continue;
      }

      const nextId=
        otherEnd(
          edgeId,
          current.vertexId
        );

      const nextVertex=
        game.board.vertices[nextId];

      if(!nextVertex) continue;

      if(
        nextVertex.building &&
        nextVertex.building.player!==player.id &&
        nextId!==targetId
      ){
        continue;
      }

      const extraCost=
        edge.road===player.id
          ?0
          :1;

      const nextCost=
        current.cost+extraCost;

      if(nextCost>maxRoads){
        continue;
      }

      if(
        nextCost>=
        (bestCost.get(nextId)??Infinity)
      ){
        continue;
      }

      bestCost.set(
        nextId,
        nextCost
      );

      queue.push({
        vertexId:nextId,
        cost:nextCost,
        roadPath:
          edge.road===player.id
            ?[...current.roadPath]
            :[
              ...current.roadPath,
              edgeId,
            ],
      });
    }
  }

  return null;
}

function cpuTurnsUntilPlayer(
  playerId,
  fromPlayerId=game.current
){
  if(!game?.playerCount) return 1;

  let distance=
    (playerId-fromPlayerId+game.playerCount)%
    game.playerCount;

  if(distance===0){
    distance=game.playerCount;
  }

  return distance;
}

function cpuSettlementContestInfo(
  player,
  targetId,
  ownRoadsNeeded=0
){
  let minOpponentRoads=99;
  let strongestThreat=0;
  let strongestOpponentId=null;

  for(const other of game.players){
    if(other.id===player.id) continue;

    const path=
      cpuExpansionPathToVertex(
        other,
        targetId,
        Math.min(
          5,
          Math.max(2,ownRoadsNeeded+2)
        )
      );

    if(!path) continue;

    const roadsNeeded=path.length;
    const turnsUntil=
      cpuTurnsUntilPlayer(
        other.id,
        player.id
      );
    const hand=totalResources(other);

    minOpponentRoads=
      Math.min(
        minOpponentRoads,
        roadsNeeded
      );

    let threat=
      Math.max(
        0,
        13-
        roadsNeeded*4.1-
        turnsUntil*.9
      );

    if(roadsNeeded===0){
      threat+=8;
    }else if(roadsNeeded===1){
      threat+=4.5;
    }

    if(hand>=8){
      threat+=3.2;
    }else if(hand>=5){
      threat+=1.6;
    }

    if(publicVP(other)>=7){
      threat+=2.4;
    }

    if(roadsNeeded<ownRoadsNeeded){
      threat+=
        (ownRoadsNeeded-roadsNeeded)*3.5;
    }

    if(threat>strongestThreat){
      strongestThreat=threat;
      strongestOpponentId=other.id;
    }
  }

  if(minOpponentRoads===99){
    return {
      minOpponentRoads:null,
      strongestThreat:0,
      strongestOpponentId:null,
      urgencyBonus:0,
      hopelessPenalty:0,
    };
  }

  let urgencyBonus=0;
  let hopelessPenalty=0;

  /*
    同程度の距離なら「先に取られる前に取る」を優先。
    逆に相手の方が大幅に近い遠距離候補は、
    無理に追い続けず別地点へ切り替える。
  */
  if(
    minOpponentRoads===0 &&
    ownRoadsNeeded<=1
  ){
    urgencyBonus=18;
  }else if(
    minOpponentRoads<=ownRoadsNeeded &&
    ownRoadsNeeded<=2
  ){
    urgencyBonus=
      8+
      strongestThreat*.45;
  }

  if(
    ownRoadsNeeded>=3 &&
    minOpponentRoads+1<ownRoadsNeeded
  ){
    hopelessPenalty=
      (ownRoadsNeeded-minOpponentRoads)*9+
      strongestThreat*.35;
  }

  return {
    minOpponentRoads,
    strongestThreat,
    strongestOpponentId,
    urgencyBonus,
    hopelessPenalty,
  };
}

function cpuTopExpansionPlans(player,limit=5){
  const candidates=
    Object.keys(game.board.vertices)
      .filter(vertexId=>
        canPlaceSettlement(
          player.id,
          vertexId,
          true
        )
      );

  const plans=[];

  for(const targetId of candidates){
    const roadPath=
      cpuExpansionPathToVertex(
        player,
        targetId,
        5
      );

    if(!roadPath) continue;

    const roadsNeeded=
      roadPath.length;

    const vertexScore=
      cpuVertexStrategicScore(
        targetId,
        player.id
      );

    const profile=
      cpuStrategyProfile(player);

    const roadPenalty=
      profile==="expand"
        ?6.2
        :profile==="balanced"
          ?7.2
          :8.4;

    const earlyBonus=
      publicVP(player)<=4
        ?7
        :publicVP(player)<=6
          ?3
          :0;

    const contest=
      cpuSettlementContestInfo(
        player,
        targetId,
        roadsNeeded
      );

    /*
      v1.49:
      競合相手が高得点なら、同じ開拓地点でも価値を上げる。
      8～9点の相手に取られる候補は「自分の得」だけではなく
      「相手の勝利を遅らせる価値」も持つ。
    */
    const contestOpponent=
      contest.strongestOpponentId===null
        ?null
        :playerById(
          contest.strongestOpponentId
        );

    const denialBonus=
      contestOpponent
        ?Math.max(
          0,
          publicVP(contestOpponent)-6
        )*3.8
        :0;

    const score=
      vertexScore*2.25-
      roadsNeeded*roadPenalty+
      earlyBonus+
      (
        roadsNeeded===0
          ?8
          :0
      )+
      contest.urgencyBonus-
      contest.hopelessPenalty+
      denialBonus;

    plans.push({
      targetId,
      roadPath,
      roadsNeeded,
      nextRoadId:
        roadPath[0]??null,
      vertexScore,
      contest,
      denialBonus,
      score,
    });
  }

  plans.sort((a,b)=>{
    if(Math.abs(b.score-a.score)>.001){
      return b.score-a.score;
    }
    return String(a.targetId).localeCompare(
      String(b.targetId)
    );
  });

  return plans.slice(
    0,
    Math.max(1,limit)
  );
}

function cpuBestExpansionPlan(player){
  return cpuTopExpansionPlans(
    player,
    1
  )[0]||null;
}

function cpuGoalDistance(
  player,
  goal,
  resources=player.resources
){
  if(!goal?.cost) return 0;

  const planCost=
    cpuGoalPlanCost(goal);

  let distance=0;

  for(const resource of RESOURCES){
    const missing=
      Math.max(
        0,
        (planCost[resource]||0)-
        (resources[resource]||0)
      );

    if(!missing) continue;

    const production=
      cpuResourceProduction(
        player,
        resource
      );

    const scarcity=
      1+
      6/
      Math.max(
        1,
        production+1
      );

    distance+=
      missing*scarcity;
  }

  return distance;
}

function cpuGoalPlanCost(goal){
  if(!goal?.cost){
    return emptyResourceCounts();
  }

  const result={...goal.cost};

  if(
    goal.kind==="road" &&
    goal.expansionTargetId &&
    goal.roadsNeeded>0
  ){
    for(const resource of RESOURCES){
      result[resource]=
        (COST.settlement[resource]||0)+
        (COST.road[resource]||0)*
        goal.roadsNeeded;
    }
  }

  return result;
}

function cpuGoalMinimumActionTurns(goal){
  if(
    goal?.kind==="road" &&
    goal.expansionTargetId &&
    goal.roadsNeeded>0
  ){
    /*
      このゲームは通常建設が1ターン1回なので、
      道路N本＋開拓地は最低でもN+1ターン必要。
    */
    return goal.roadsNeeded+1;
  }

  return 1;
}

function cpuResourceExpectedPerTurn(
  player,
  resource
){
  const direct=
    cpuResourceProduction(
      player,
      resource
    )/36;

  let tradeFlow=0;

  for(const produced of RESOURCES){
    if(produced===resource) continue;

    const rate=
      Math.max(
        2,
        getTradeRate(
          player,
          produced
        )||4
      );

    tradeFlow+=
      (
        cpuResourceProduction(
          player,
          produced
        )/36
      )/rate;
  }

  /*
    他資源は建設にも使うので、全量を交易へ回すとは見なさない。
  */
  return direct+tradeFlow*.42;
}

function cpuGoalEta(
  player,
  goal,
  resources=player.resources
){
  if(!goal?.cost) return 99;

  const planCost=
    cpuGoalPlanCost(goal);

  let resourceEta=0;
  let missingTotal=0;

  for(const resource of RESOURCES){
    const missing=
      Math.max(
        0,
        (planCost[resource]||0)-
        (resources[resource]||0)
      );

    if(!missing) continue;

    missingTotal+=missing;

    const expected=
      cpuResourceExpectedPerTurn(
        player,
        resource
      );

    const turns=
      missing/
      Math.max(.055,expected);

    resourceEta=
      Math.max(
        resourceEta,
        turns
      );
  }

  const minimumTurns=
    cpuGoalMinimumActionTurns(goal);

  let eta=
    Math.max(
      minimumTurns,
      resourceEta
    );

  /*
    7枚超えで必要資源を抱える長期計画は少し不安定。
  */
  if(
    totalResources(player)>=8 &&
    missingTotal>=2
  ){
    eta+=.35;
  }

  return Math.min(20,eta);
}

function cpuHiddenVictoryPointCount(player){
  if(!player?.dev) return 0;
  return player.dev.reduce(
    (count,card)=>count+(card==="vp"?1:0),
    0
  );
}

/*
  CPU自身は手札の勝利点カードを知っているため、
  勝ち筋評価では未公開VPも含める。
  実際の勝利判定(totalVP/checkVictory)は従来ルールのまま。
*/
function cpuPlanningVP(player){
  return (player?totalVP(player):0)+
    cpuHiddenVictoryPointCount(player);
}

function cpuGoalProductionGain(player,goal){
  if(!goal) return 0;

  if(
    goal.kind==="settlement" &&
    goal.targetId
  ){
    return (
      vertexProductionScore(
        goal.targetId
      )/5
    );
  }

  if(
    goal.kind==="city" &&
    goal.targetId
  ){
    /*
      都市化で増えるのは、その開拓地1軒分と同じ追加生産。
    */
    return (
      vertexProductionScore(
        goal.targetId
      )/5
    );
  }

  if(
    goal.kind==="road" &&
    goal.expansionTargetId
  ){
    return (
      vertexProductionScore(
        goal.expansionTargetId
      )/5
    )/
    Math.max(1,goal.roadsNeeded);
  }

  return 0;
}

function cpuGoalAwardValue(player,goal){
  let value=0;

  if(goal?.kind==="dev"){
    const maxOpponentKnights=
      Math.max(
        0,
        ...game.players
          .filter(other=>other.id!==player.id)
          .map(other=>other.knightsPlayed||0)
      );

    const gap=
      maxOpponentKnights-
      (player.knightsPlayed||0);

    if(!player.hasLargestArmy){
      if(gap<=0){
        value+=13;
      }else if(gap===1){
        value+=8;
      }else if(gap===2){
        value+=3;
      }
    }
  }

  if(goal?.kind==="road"){
    const plan=goal.roadAwardPlan||null;
    const opponentMaximum=Math.max(
      0,
      ...game.players
        .filter(other=>other.id!==player.id)
        .map(other=>other.longestRoad||0)
    );

    /*
      v1.55:
      最長交易路は「近いだけ」で高評価にしない。
      実際に+2VPを取れる道路列だけを明確に加点し、
      すでに保持中の防衛は終盤かつ僅差時だけ小さく評価する。
    */
    if(plan?.awardGain>0){
      value+=cpuPlanningVP(player)>=7?18:11;
    }else if(
      player.hasLongestRoad &&
      plan?.wouldHold &&
      opponentMaximum>=
        (player.longestRoad||0)-1
    ){
      value+=cpuPlanningVP(player)>=8?8:3;
    }
  }

  return value;
}

function cpuProjectedLongestRoad(
  player,
  edgeId
){
  const edge=game.board.edges[edgeId];

  if(
    !edge ||
    edge.road!==null
  ){
    return player.longestRoad||0;
  }

  edge.road=player.id;
  player.roads.push(edgeId);

  let projected=0;

  try{
    projected=
      calculateLongestRoad(player.id);
  }finally{
    player.roads.pop();
    edge.road=null;
  }

  return projected;
}

function cpuRoadAwardGain(player,goal){
  if(
    goal?.kind!=="road" ||
    !goal.targetId ||
    !canPlaceRoad(
      player.id,
      goal.targetId
    )
  ){
    return 0;
  }

  const projected=
    cpuProjectedLongestRoad(
      player,
      goal.targetId
    );

  if(projected<5){
    return 0;
  }

  const opponentMaximum=
    Math.max(
      0,
      ...game.players
        .filter(other=>other.id!==player.id)
        .map(other=>other.longestRoad||0)
    );

  const wouldHold=
    player.hasLongestRoad
      ?projected>=opponentMaximum
      :projected>opponentMaximum;

  return (
    wouldHold &&
    !player.hasLongestRoad
  )
    ?2
    :0;
}

function cpuGoalImmediatePointGain(player,goal){
  if(!goal) return 0;

  let gain=0;

  if(
    goal.kind==="city" ||
    goal.kind==="settlement"
  ){
    gain+=1;
  }

  gain+=
    cpuRoadAwardGain(
      player,
      goal
    );

  return gain;
}

function cpuGoalTacticalWinBonus(player,goal){
  if(
    !goal ||
    !cpuGoalBuildable(
      player,
      goal
    )
  ){
    return 0;
  }

  const gain=
    cpuGoalImmediatePointGain(
      player,
      goal
    );

  if(!gain) return 0;

  const needed=
    Math.max(
      0,
      victoryTarget(player)-
      cpuPlanningVP(player)
    );

  if(
    needed>0 &&
    gain>=needed
  ){
    /* 勝てる手は他の長期評価より必ず優先する。 */
    return 260;
  }

  if(cpuPlanningVP(player)>=7){
    return gain*34;
  }

  return gain*9;
}

function cpuGoalOutcomeValue(player,goal){
  const points=cpuPlanningVP(player);
  let value=0;

  if(
    goal.kind==="settlement" ||
    goal.kind==="city"
  ){
    value+=14;

    if(points>=7){
      value+=12;
    }
  }

  if(
    goal.kind==="road" &&
    goal.expansionTargetId
  ){
    value+=9;
  }

  if(goal.kind==="dev"){
    value+=
      points>=7
        ?10
        :5;
  }

  value+=
    cpuGoalProductionGain(
      player,
      goal
    )*3.4;

  value+=
    cpuGoalAwardValue(
      player,
      goal
    );

  value+=
    cpuGoalTacticalWinBonus(
      player,
      goal
    );

  return value;
}

function cpuRoadOpportunityPenalty(player,goal){
  if(!player || goal?.kind!=="road") return 0;

  /* 開拓地へ向かう街道は必要経費なので原則ここでは罰しない。 */
  if(goal.expansionTargetId){
    const extra=Math.max(0,(goal.roadsNeeded||1)-3);
    return extra*5;
  }

  const plan=goal.roadAwardPlan||null;
  if(plan?.immediateWin) return 0;

  const opponentMaximum=Math.max(
    0,
    ...game.players
      .filter(other=>other.id!==player.id)
      .map(other=>other.longestRoad||0)
  );

  let penalty=0;

  if(plan?.awardGain>0){
    const length=Math.max(1,plan.sequence?.length||1);
    const margin=(plan.projectedLongest||0)-opponentMaximum;

    /* 2点を取れても、複数本必要・奪い返されやすいなら割引。 */
    penalty+=Math.max(0,length-1)*15;
    if(margin<=0) penalty+=22;
    else if(margin===1) penalty+=12;

    penalty+=Math.max(0,player.roads.length-7)*4.5;
  }else{
    /*
      VPにも開拓にも直結しない街道を強く抑える。
      特に既に最長交易路を持っている時の延長競争を止める。
    */
    penalty+=20;
    penalty+=Math.max(0,player.roads.length-6)*6;
    if(player.hasLongestRoad) penalty+=28;
  }

  /* 開拓地駒を使い切っているなら都市・発展カードへ寄せる。 */
  if(
    player.pieces.settlement<=0 &&
    player.settlements.length>0
  ){
    penalty+=18;
  }

  return penalty;
}

function cpuGoalKey(goal){
  if(!goal) return null;

  if(
    goal.kind==="road" &&
    goal.expansionTargetId
  ){
    return `expand:${goal.expansionTargetId}`;
  }

  if(goal.targetId!==null && goal.targetId!==undefined){
    return `${goal.kind}:${goal.targetId}`;
  }

  return goal.kind;
}

function cpuRememberPlan(player,goal){
  if(!player || !goal) return;

  player.cpuPlan={
    key:cpuGoalKey(goal),
    kind:goal.kind,
    targetId:goal.targetId??null,
    expansionTargetId:
      goal.expansionTargetId??null,
    round:game.turnNo||0,
    score:goal.strategicScore||0,
  };
}

function cpuPersistentGoal(player,goals){
  const plan=player?.cpuPlan;
  if(!plan || !goals.length) return null;

  const age=
    (game.turnNo||0)-
    (plan.round||0);

  if(age>2){
    return null;
  }

  return goals.find(
    goal=>cpuGoalKey(goal)===plan.key
  )||null;
}

function cpuGoalBuildable(player,goal){
  if(!player || !goal) return false;

  if(!hasCost(player,goal.cost)){
    return false;
  }

  if(goal.kind==="city"){
    return (
      player.pieces.city>0 &&
      canUpgradeCity(
        player.id,
        goal.targetId
      )
    );
  }

  if(goal.kind==="settlement"){
    return (
      player.pieces.settlement>0 &&
      canPlaceSettlement(
        player.id,
        goal.targetId,
        false
      )
    );
  }

  if(goal.kind==="road"){
    return (
      player.pieces.road>0 &&
      !!goal.targetId &&
      canPlaceRoad(
        player.id,
        goal.targetId
      )
    );
  }

  if(goal.kind==="dev"){
    return game.devDeck.length>0;
  }

  return false;
}

function cpuExecuteGoal(player,goal){
  if(!cpuGoalBuildable(player,goal)){
    return false;
  }

  const analysisGoal=
    cpuAnalysisGoalSummary(
      player,
      goal
    );

  if(goal.kind==="city"){
    placeCity(
      player.id,
      goal.targetId
    );
    player.builtThisTurn=true;
    cpuAnalysisRecordAction(
      player,
      "build_city",
      {goal:analysisGoal}
    );
    log(`${player.name}が都市を建てました。`);
    return true;
  }

  if(goal.kind==="settlement"){
    payCost(
      player,
      COST.settlement,
      "開拓地建設"
    );

    placeSettlement(
      player.id,
      goal.targetId,
      false
    );

    player.builtThisTurn=true;
    cpuAnalysisRecordAction(
      player,
      "build_settlement",
      {goal:analysisGoal}
    );
    log(`${player.name}が開拓地を建てました。`);
    return true;
  }

  if(goal.kind==="road"){
    placeRoad(
      player.id,
      goal.targetId,
      false
    );

    player.builtThisTurn=true;
    cpuAnalysisRecordAction(
      player,
      "build_road",
      {goal:analysisGoal}
    );
    log(`${player.name}が街道を建てました。`);
    return true;
  }

  if(goal.kind==="dev"){
    const bought=buyDev(player.id);
    if(bought){
      cpuAnalysisRecordAction(
        player,
        "buy_development",
        {goal:analysisGoal}
      );
    }
    return bought;
  }

  return false;
}



function cpuSimulatedResources(
  player,
  delta
){
  const simulated={
    ...player.resources,
  };

  for(const resource of RESOURCES){
    simulated[resource]=
      Math.max(
        0,
        (simulated[resource]||0)+
        (delta[resource]||0)
      );
  }

  return simulated;
}

function cpuCityTargetScore(vertexId,playerId){
  const vertex=game.board.vertices[vertexId];
  if(!vertex) return -9999;

  const production=
    vertexProductionScore(vertexId);

  let score=
    production*1.65+
    cpuVertexStrategicScore(
      vertexId,
      playerId
    )*.55;

  for(const hexId of vertex.hexes){
    const resource=
      game.board.hexes[hexId]?.resource;

    if(resource==="grain"){
      score+=1.15;
    }

    if(resource==="ore"){
      score+=1.25;
    }
  }

  return score;
}

function cpuTopSettlementTargets(player,limit=3){
  const candidates=
    Object.keys(game.board.vertices)
      .filter(vertexId=>
        canPlaceSettlement(
          player.id,
          vertexId,
          false
        )
      );

  if(!candidates.length) return [];

  const expansionPlans=
    cpuTopExpansionPlans(
      player,
      5
    );

  const expansionScoreByTarget=
    new Map(
      expansionPlans.map(plan=>[
        plan.targetId,
        8+
        plan.contest.urgencyBonus*.35+
        (plan.denialBonus||0)*.45,
      ])
    );

  const scored=candidates.map(id=>({
    id,
    score:
      cpuVertexStrategicScore(
        id,
        player.id
      )+
      (expansionScoreByTarget.get(id)||0),
  }));

  scored.sort((a,b)=>{
    if(Math.abs(b.score-a.score)>.001){
      return b.score-a.score;
    }
    return String(a.id).localeCompare(
      String(b.id)
    );
  });

  return scored.slice(
    0,
    Math.max(1,limit)
  );
}

function cpuBestSettlementTarget(player){
  return cpuTopSettlementTargets(
    player,
    1
  )[0]||null;
}

function cpuTopCityTargets(player,limit=3){
  if(!player.settlements.length){
    return [];
  }

  const candidates=
    [...player.settlements]
      .filter(vertexId=>
        canUpgradeCity(
          player.id,
          vertexId
        )
      )
      .map(id=>({
        id,
        score:
          cpuCityTargetScore(
            id,
            player.id
          ),
      }));

  candidates.sort((a,b)=>{
    if(Math.abs(b.score-a.score)>.001){
      return b.score-a.score;
    }
    return String(a.id).localeCompare(
      String(b.id)
    );
  });

  return candidates.slice(
    0,
    Math.max(1,limit)
  );
}

function cpuBestCityTarget(player){
  return cpuTopCityTargets(
    player,
    1
  )[0]||null;
}

function cpuResourceMissingCount(player,cost){
  if(!cost) return 0;

  return RESOURCES.reduce(
    (sum,resource)=>
      sum+
      Math.max(
        0,
        (cost[resource]||0)-
        (player.resources[resource]||0)
      ),
    0
  );
}

function cpuVertexExpectedResourceRates(vertexId){
  const result=Object.fromEntries(
    RESOURCES.map(resource=>[resource,0])
  );

  const vertex=game.board.vertices[vertexId];
  if(!vertex) return result;

  for(const hexId of vertex.hexes){
    const hex=game.board.hexes[hexId];
    if(!hex || !RESOURCES.includes(hex.resource)){
      continue;
    }

    const pips=hex.number
      ?(PIPS[hex.number]||0)
      :0;

    result[hex.resource]+=pips/36;
  }

  return result;
}

function cpuPlannerInitialRates(player){
  const rates={};

  for(const resource of RESOURCES){
    rates[resource]=
      Math.max(
        .02,
        cpuResourceExpectedPerTurn(
          player,
          resource
        )
      );
  }

  return rates;
}

function cpuPlannerCostForExpansion(plan){
  const cost=emptyResourceCounts();

  for(const resource of RESOURCES){
    cost[resource]=
      (COST.settlement[resource]||0)+
      (COST.road[resource]||0)*
      plan.roadsNeeded;
  }

  return cost;
}

function cpuPlannerMacros(player,goals){
  const macros=[];

  for(const plan of cpuTopExpansionPlans(player,4)){
    if(player.pieces.settlement<=0) break;
    if(plan.roadsNeeded>player.pieces.road) continue;

    macros.push({
      key:
        plan.roadsNeeded>0
          ?`expand:${plan.targetId}`
          :`settlement:${plan.targetId}`,
      kind:"expand",
      targetId:plan.targetId,
      cost:cpuPlannerCostForExpansion(plan),
      actionTurns:plan.roadsNeeded+1,
      roadsUsed:plan.roadsNeeded,
      settlementUsed:1,
      vpGain:1,
      rateGain:
        cpuVertexExpectedResourceRates(
          plan.targetId
        ),
      utility:
        plan.vertexScore*1.35+
        plan.contest.urgencyBonus*.8-
        plan.contest.hopelessPenalty*.45+
        (plan.denialBonus||0)*.8,
      unique:true,
    });
  }

  for(const target of cpuTopCityTargets(player,3)){
    macros.push({
      key:`city:${target.id}`,
      kind:"city",
      targetId:target.id,
      cost:{...COST.city},
      actionTurns:1,
      cityUsed:1,
      vpGain:1,
      rateGain:
        cpuVertexExpectedResourceRates(
          target.id
        ),
      utility:target.score*.82,
      unique:true,
    });
  }

  if(game.devDeck.length){
    const maxOpponentKnights=Math.max(
      0,
      ...game.players
        .filter(other=>other.id!==player.id)
        .map(other=>other.knightsPlayed||0)
    );

    const knightGap=
      maxOpponentKnights-
      (player.knightsPlayed||0);

    let devUtility=8;
    if(!player.hasLargestArmy){
      if(knightGap<=0) devUtility+=16;
      else if(knightGap===1) devUtility+=11;
      else if(knightGap===2) devUtility+=5;
    }
    if(cpuPlanningVP(player)>=7) devUtility+=9;

    macros.push({
      key:"dev",
      kind:"dev",
      targetId:null,
      cost:{...COST.dev},
      actionTurns:1,
      vpGain:.20,
      rateGain:emptyResourceCounts(),
      utility:devUtility,
      unique:false,
    });
  }

  const roadSequence=
    cpuBestRoadSequence(
      player,
      Math.min(4,player.pieces.road)
    );

  const roadDefenseThreat=
    player.hasLongestRoad &&
    Math.max(
      0,
      ...game.players
        .filter(other=>other.id!==player.id)
        .map(other=>other.longestRoad||0)
    )>=
      (player.longestRoad||0)-1;

  if(
    roadSequence?.sequence?.length &&
    (
      roadSequence.awardGain>0 ||
      (
        roadDefenseThreat &&
        cpuPlanningVP(player)>=8 &&
        roadSequence.sequence.length===1
      )
    )
  ){
    const cost=emptyResourceCounts();
    for(const resource of RESOURCES){
      cost[resource]=
        (COST.road[resource]||0)*
        roadSequence.sequence.length;
    }

    macros.push({
      key:`road:${roadSequence.sequence[0]}`,
      kind:"roadAward",
      targetId:roadSequence.sequence[0],
      cost,
      actionTurns:roadSequence.sequence.length,
      roadsUsed:roadSequence.sequence.length,
      vpGain:roadSequence.awardGain||0,
      rateGain:emptyResourceCounts(),
      utility:
        (roadSequence.awardGain||0)*30+
        (roadDefenseThreat?8:0)-
        roadSequence.sequence.length*8-
        Math.max(0,player.roads.length-7)*4,
      unique:true,
    });
  }

  /*
    現在の即時候補がマクロ一覧から漏れた場合も、
    1手目として比較対象には残す。
  */
  for(const goal of goals){
    const key=cpuGoalKey(goal);
    if(macros.some(macro=>macro.key===key)) continue;

    macros.push({
      key,
      kind:goal.kind,
      targetId:goal.targetId??null,
      cost:cpuGoalPlanCost(goal),
      actionTurns:cpuGoalMinimumActionTurns(goal),
      roadsUsed:goal.kind==="road"?1:0,
      settlementUsed:goal.kind==="settlement"?1:0,
      cityUsed:goal.kind==="city"?1:0,
      vpGain:cpuGoalImmediatePointGain(player,goal),
      rateGain:emptyResourceCounts(),
      utility:Math.max(0,goal.boardScore||0)*.35,
      unique:true,
    });
  }

  return macros;
}

function cpuPlannerMacroApplicable(state,macro){
  if(macro.unique && state.used.has(macro.key)){
    return false;
  }

  if(
    (macro.roadsUsed||0)>
    state.roadPieces
  ){
    return false;
  }

  if(
    (macro.settlementUsed||0)>
    state.settlementPieces
  ){
    return false;
  }

  if(
    (macro.cityUsed||0)>
    state.cityPieces
  ){
    return false;
  }

  if(
    macro.kind==="city" &&
    state.settlements<=0
  ){
    return false;
  }

  if(
    macro.kind==="dev" &&
    state.devRemaining<=0
  ){
    return false;
  }

  return true;
}

function cpuPlannerEta(state,macro){
  let resourceEta=0;

  for(const resource of RESOURCES){
    const missing=Math.max(
      0,
      (macro.cost[resource]||0)-
      (state.resources[resource]||0)
    );

    if(!missing) continue;

    resourceEta=Math.max(
      resourceEta,
      missing/
        Math.max(
          .035,
          state.rates[resource]||0
        )
    );
  }

  return Math.min(
    18,
    Math.max(
      macro.actionTurns||1,
      resourceEta
    )
  );
}

function cpuPlannerApplyMacro(state,macro,depth){
  const next={
    ...state,
    resources:{...state.resources},
    rates:{...state.rates},
    used:new Set(state.used),
  };

  const eta=cpuPlannerEta(
    state,
    macro
  );

  for(const resource of RESOURCES){
    next.resources[resource]=
      Math.max(
        0,
        (next.resources[resource]||0)+
        (next.rates[resource]||0)*eta-
        (macro.cost[resource]||0)
      );
  }

  next.turns+=eta;
  next.vp+=macro.vpGain||0;
  next.roadPieces-=
    macro.roadsUsed||0;
  next.settlementPieces-=
    macro.settlementUsed||0;
  next.cityPieces-=
    macro.cityUsed||0;

  if(macro.kind==="expand"){
    next.settlements++;
  }else if(macro.kind==="city"){
    next.settlements--;
    next.cities++;
    next.settlementPieces++;
  }else if(macro.kind==="dev"){
    next.devRemaining--;
    next.devBuys++;
  }

  for(const resource of RESOURCES){
    next.rates[resource]+=
      macro.rateGain?.[resource]||0;
  }

  next.utility+=
    (macro.utility||0)/
    (1+depth*.32);

  if(macro.unique){
    next.used.add(macro.key);
  }

  if(!next.firstKey){
    next.firstKey=macro.key;
  }

  next.depth=depth+1;
  return next;
}

function cpuPlannerStateScore(player,state){
  const target=victoryTarget(player);
  const rateTotal=RESOURCES.reduce(
    (sum,resource)=>
      sum+(state.rates[resource]||0),
    0
  );

  const resourceReserve=RESOURCES.reduce(
    (sum,resource)=>
      sum+Math.min(3,state.resources[resource]||0),
    0
  );

  if(state.vp>=target){
    return (
      20000-
      state.turns*520+
      rateTotal*55+
      state.utility*2
    );
  }

  const gap=Math.max(0,target-state.vp);

  /*
    未探索部分は、生産力が高いほど残りVPを早く取れると近似。
    勝利までのターンを強く罰するため、見た目の生産力より
    実際に10点へ近い系列を優先する。
  */
  const pointVelocity=
    Math.max(
      .10,
      .10+
      rateTotal*.13+
      state.devBuys*.025
    );

  const tailTurns=
    gap/pointVelocity;

  return (
    state.vp*255-
    (state.turns+tailTurns)*46+
    rateTotal*72+
    resourceReserve*2.2+
    state.utility*1.7
  );
}

function cpuLookaheadScores(player,goals){
  const macros=cpuPlannerMacros(
    player,
    goals
  );

  if(!macros.length){
    return new Map();
  }

  const initial={
    resources:{...player.resources},
    rates:cpuPlannerInitialRates(player),
    vp:
      totalVP(player)+
      player.dev.filter(card=>card==="vp").length,
    turns:0,
    utility:0,
    roadPieces:player.pieces.road,
    settlementPieces:player.pieces.settlement,
    cityPieces:player.pieces.city,
    settlements:player.settlements.length,
    cities:player.cities.length,
    devRemaining:game.devDeck.length,
    devBuys:0,
    used:new Set(),
    firstKey:null,
    depth:0,
  };

  const depthLimit=
    cpuPlanningVP(player)>=7
      ?5
      :4;

  const beamWidth=
    cpuPlanningVP(player)>=7
      ?16
      :12;

  let beam=[initial];
  const bestByFirst=new Map();

  for(let depth=0;depth<depthLimit;depth++){
    const next=[];

    for(const state of beam){
      for(const macro of macros){
        if(!cpuPlannerMacroApplicable(state,macro)){
          continue;
        }

        const child=
          cpuPlannerApplyMacro(
            state,
            macro,
            depth
          );

        const score=
          cpuPlannerStateScore(
            player,
            child
          );

        child._plannerScore=score;
        next.push(child);

        if(child.firstKey){
          const old=
            bestByFirst.get(child.firstKey);
          if(old===undefined || score>old){
            bestByFirst.set(
              child.firstKey,
              score
            );
          }
        }
      }
    }

    if(!next.length) break;

    next.sort(
      (a,b)=>
        b._plannerScore-
        a._plannerScore
    );

    beam=next.slice(0,beamWidth);
  }

  return bestByFirst;
}

function cpuApplyLookaheadToGoals(player,goals){
  if(goals.length<=1) return goals;

  const lookahead=
    cpuLookaheadScores(
      player,
      goals
    );

  if(!lookahead.size){
    return goals;
  }

  const available=goals
    .map(goal=>({
      key:cpuGoalKey(goal),
      value:lookahead.get(
        cpuGoalKey(goal)
      ),
    }))
    .filter(item=>
      Number.isFinite(item.value)
    );

  if(!available.length){
    return goals;
  }

  const best=Math.max(
    ...available.map(item=>item.value)
  );

  const endgame=
    cpuPlanningVP(player)>=7;

  return goals.map(goal=>{
    const value=
      lookahead.get(
        cpuGoalKey(goal)
      );

    if(!Number.isFinite(value)){
      return {
        ...goal,
        lookaheadScore:null,
        lookaheadBonus:-8,
        strategicScore:
          goal.strategicScore-8,
      };
    }

    const gap=best-value;
    const maximumBonus=endgame?68:48;
    const bonus=Math.max(
      -12,
      maximumBonus-
      gap*(endgame?.115:.095)
    );

    return {
      ...goal,
      lookaheadScore:value,
      lookaheadBonus:bonus,
      strategicScore:
        goal.strategicScore+
        bonus,
    };
  });
}

function cpuStrategicGoalSignature(player){
  const boardSignature=game.board.hexes
    .map(hex=>
      `${hex.resource}:${hex.number||0}:`+
      `${hex.lakeNumbers?.join(".")||""}`
    )
    .join("|");

  const playersSignature=game.players
    .map(other=>[
      other.id,
      publicVP(other),
      totalResources(other),
      other.roads.length,
      other.settlements.length,
      other.cities.length,
      other.knightsPlayed||0,
      other.hasLongestRoad?1:0,
      other.hasLargestArmy?1:0,
    ].join(","))
    .join(";");

  const resources=RESOURCES
    .map(resource=>player.resources[resource]||0)
    .join(",");

  return [
    game.turnSerial,
    game.turnNo,
    game.current,
    game.phase,
    game.robberHex??"none",
    game.devDeck.length,
    player.id,
    resources,
    player.pieces.road,
    player.pieces.settlement,
    player.pieces.city,
    player.roads.join("."),
    player.settlements.join("."),
    player.cities.join("."),
    player.dev.join("."),
    game.oldBootHolder??"none",
    playersSignature,
    boardSignature,
  ].join("#");
}

function cpuStrategicGoals(player){
  const cacheSignature=
    cpuStrategicGoalSignature(player);

  const cached=
    cpuStrategicGoalCache.get(player.id);

  if(
    cached?.signature===cacheSignature
  ){
    return cached.goals;
  }

  const goals=[];

  const points=cpuPlanningVP(player);
  const profile=cpuStrategyProfile(player);

  const expansions=
    player.pieces.settlement>0
      ?cpuTopExpansionPlans(player,3)
      :[];

  const cityTargets=
    player.pieces.city>0
      ?cpuTopCityTargets(player,3)
      :[];

  const settlementTargets=
    player.pieces.settlement>0
      ?cpuTopSettlementTargets(player,3)
      :[];

  for(const settlementTarget of settlementTargets){
    let base=
      points<=4
        ?132
        :points<=6
          ?122
          :116;

    if(profile==="expand") base+=4;
    else if(profile==="city") base-=2;

    goals.push({
      kind:"settlement",
      cost:COST.settlement,
      targetId:settlementTarget.id,
      boardScore:settlementTarget.score,
      base,
    });
  }

  for(const expansion of expansions){
    if(
      expansion.roadsNeeded<=0 ||
      player.pieces.road<=0
    ){
      continue;
    }

    let base=
      points<=4
        ?126
        :points<=6
          ?111
          :94;

    if(profile==="expand") base+=5;
    else if(profile==="city") base-=3;

    goals.push({
      kind:"road",
      cost:COST.road,
      targetId:expansion.nextRoadId,
      boardScore:expansion.score,
      expansionTargetId:expansion.targetId,
      roadsNeeded:expansion.roadsNeeded,
      contest:expansion.contest,
      denialBonus:expansion.denialBonus||0,
      base,
    });
  }

  for(const cityTarget of cityTargets){
    let base=
      points<=4
        ?108
        :points<=7
          ?128
          :140;

    if(profile==="city") base+=6;
    else if(profile==="expand") base-=2;

    goals.push({
      kind:"city",
      cost:COST.city,
      targetId:cityTarget.id,
      boardScore:cityTarget.score,
      base,
    });
  }

  const roadTarget=
    player.pieces.road>0
      ?cpuBestRoadTarget(player)
      :null;

  if(roadTarget){
    const duplicate=goals.some(goal=>
      goal.kind==="road" &&
      goal.targetId===roadTarget.id &&
      goal.expansionTargetId===
        (roadTarget.expansionTargetId??null)
    );

    if(!duplicate){
      const longestLeader=Math.max(
        ...game.players.map(
          other=>other.longestRoad||0
        )
      );

      const awardRace=
        roadTarget.awardGain>0
          ?46
          :(
            player.longestRoad>=3 &&
            player.longestRoad>=longestLeader-2
          )
            ?20
            :0;

      goals.push({
        kind:"road",
        cost:COST.road,
        targetId:roadTarget.id,
        boardScore:roadTarget.score,
        roadAwardPlan:
          roadTarget.roadAwardPlan||null,
        base:60+awardRace,
      });
    }
  }

  if(game.devDeck.length){
    const largestArmyHolder=
      game.players.find(
        other=>other.hasLargestArmy
      );

    const maximumOpponentKnights=Math.max(
      0,
      ...game.players
        .filter(other=>other.id!==player.id)
        .map(other=>other.knightsPlayed||0)
    );

    const armyPressure=
      (
        player.knightsPlayed<=
        maximumOpponentKnights+1 ||
        !largestArmyHolder
      )
        ?12
        :4;

    let base=
      points<=4
        ?58
        :points<=7
          ?84
          :102;

    if(profile==="city") base+=3;

    goals.push({
      kind:"dev",
      cost:COST.dev,
      targetId:null,
      boardScore:0,
      base:base+armyPressure,
    });
  }

  let scored=goals.map(goal=>{
    const missing=cpuResourceMissingCount(
      player,
      goal.cost
    );

    const distance=cpuGoalDistance(
      player,
      goal
    );

    const eta=cpuGoalEta(
      player,
      goal
    );

    const outcomeValue=cpuGoalOutcomeValue(
      player,
      goal
    );

    const roadOpportunityPenalty=
      cpuRoadOpportunityPenalty(
        player,
        goal
      );

    let contestAdjustment=0;

    if(goal.contest){
      contestAdjustment+=
        goal.contest.urgencyBonus*.75-
        goal.contest.hopelessPenalty*.85+
        (goal.denialBonus||0)*.75;
    }

    return {
      ...goal,
      missing,
      distance,
      eta,
      outcomeValue,
      roadOpportunityPenalty,
      strategicScore:
        goal.base+
        goal.boardScore*.68+
        outcomeValue+
        contestAdjustment-
        roadOpportunityPenalty-
        distance*4.4-
        eta*7.2,
    };
  });

  scored=cpuApplyLookaheadToGoals(
    player,
    scored
  );

  const result=scored.sort((a,b)=>{
    if(
      Math.abs(
        b.strategicScore-
        a.strategicScore
      )>.001
    ){
      return (
        b.strategicScore-
        a.strategicScore
      );
    }

    return String(cpuGoalKey(a)).localeCompare(
      String(cpuGoalKey(b))
    );
  });

  cpuStrategicGoalCache.set(
    player.id,
    {
      signature:cacheSignature,
      goals:result,
    }
  );

  return result;
}

function cpuChooseGoal(player){
  const goals=
    cpuStrategicGoals(player);

  if(!goals.length){
    return null;
  }

  const best=goals[0];

  /*
    他プレイヤーの交易受諾判定などでは、
    勝手にそのCPUの長期計画を書き換えない。
  */
  const canPersist=
    !player.human &&
    game.current===player.id &&
    game.phase==="turn";

  if(!canPersist){
    return best;
  }

  const persistent=
    cpuPersistentGoal(
      player,
      goals
    );

  let selected=best;

  if(persistent){
    /*
      少し良い程度では目標変更しない。
      ただし探索層が明確に優位と判断した時は早めに乗り換える。
    */
    if(
      best.strategicScore<
      persistent.strategicScore+12
    ){
      selected=persistent;
    }
  }

  const selectedKey=
    cpuGoalKey(selected);

  if(
    !player.cpuPlan ||
    player.cpuPlan.key!==selectedKey
  ){
    cpuRememberPlan(
      player,
      selected
    );
  }else{
    player.cpuPlan.score=
      selected.strategicScore||0;
  }

  return selected;
}

function cpuResourceKeepValue(
  player,
  resource,
  goal=null
){
  const selectedGoal=
    goal||cpuChooseGoal(player);

  const production=
    cpuResourceProduction(
      player,
      resource
    );

  const selectedPlanCost=
    selectedGoal?.cost
      ?cpuGoalPlanCost(selectedGoal)
      :null;

  const goalNeed=
    selectedPlanCost?.[resource]||0;

  const owned=
    player.resources[resource]||0;

  let value=1;

  if(production<=0){
    value+=2.7;
  }else if(production<=2){
    value+=1.45;
  }else if(production>=6){
    value-=.45;
  }

  if(goalNeed>0){
    if(owned<=goalNeed){
      value+=5.1;
    }else if(owned===goalNeed+1){
      value+=2.2;
    }
  }

  if(resource==="grain"){
    value+=1.05;
  }else if(resource==="ore"){
    value+=
      player.settlements.length>=2
        ?1.15
        :.45;
  }else if(
    resource==="wood" ||
    resource==="brick"
  ){
    if(player.pieces.settlement>0){
      value+=.65;
    }
  }

  const excess=
    Math.max(
      0,
      owned-goalNeed-1
    );

  value-=Math.min(2.4,excess*.48);

  const tradeRate=
    getTradeRate(
      player,
      resource
    );

  if(
    owned>=tradeRate &&
    excess>=tradeRate
  ){
    value-=.5;
  }

  return value;
}

function cpuChooseDiscardResource(player){
  const goal=cpuChooseGoal(player);

  const candidates=
    RESOURCES.filter(
      resource=>
        player.resources[resource]>0
    );

  if(!candidates.length){
    return null;
  }

  candidates.sort((a,b)=>{
    const valueDifference=
      cpuResourceKeepValue(
        player,
        a,
        goal
      )-
      cpuResourceKeepValue(
        player,
        b,
        goal
      );

    if(
      Math.abs(valueDifference)>.001
    ){
      return valueDifference;
    }

    return (
      player.resources[b]-
      player.resources[a]
    );
  });

  return candidates[0];
}

function cpuVictimScore(victim,thief=null){
  if(!victim) return -9999;

  const points=publicVP(victim);
  const resources=totalResources(victim);

  let score=
    points*4.2+
    resources*1.1;

  if(victim.hasLongestRoad){
    score+=3.5;
  }

  if(victim.hasLargestArmy){
    score+=3.5;
  }

  if(
    thief &&
    points>publicVP(thief)
  ){
    score+=
      (points-publicVP(thief))*2.2;
  }

  return score;
}

function cpuChooseVictimFromCandidates(
  candidates,
  thiefId
){
  if(!candidates?.length) return null;

  const thief=playerById(thiefId);

  return [...candidates]
    .sort(
      (a,b)=>
        cpuVictimScore(b,thief)-
        cpuVictimScore(a,thief)
    )[0]||null;
}

function cpuGoalMissingResources(player,goal){
  if(!goal?.cost) return [];

  const planCost=
    cpuGoalPlanCost(goal);

  return RESOURCES
    .map(resource=>({
      resource,
      missing:
        Math.max(
          0,
          (planCost[resource]||0)-
          player.resources[resource]
        ),
    }))
    .filter(item=>item.missing>0)
    .sort((a,b)=>{
      if(b.missing!==a.missing){
        return b.missing-a.missing;
      }

      return (
        cpuResourceKeepValue(
          player,
          b.resource,
          goal
        )-
        cpuResourceKeepValue(
          player,
          a.resource,
          goal
        )
      );
    });
}

function cpuMonopolyResourceScore(
  player,
  resource,
  goal=null
){
  const supply=
    expectedResourceSupply();

  const othersTotal=
    Math.max(
      0,
      supply-
      (game.bank[resource]||0)-
      (player.resources[resource]||0)
    );

  const selectedGoal=
    goal||cpuChooseGoal(player);

  const planCost=
    selectedGoal?.cost
      ?cpuGoalPlanCost(selectedGoal)
      :emptyResourceCounts();

  const missing=Math.max(
    0,
    (planCost[resource]||0)-
    (player.resources[resource]||0)
  );

  const simulated={
    ...player.resources,
    [resource]:
      (player.resources[resource]||0)+
      othersTotal,
  };

  const improvement=
    selectedGoal
      ?cpuGoalDistance(
        player,
        selectedGoal
      )-
      cpuGoalDistance(
        player,
        selectedGoal,
        simulated
      )
      :0;

  const immediateWin=
    cpuCanImmediateWinWithResources(
      player,
      simulated
    );

  return {
    resource,
    othersTotal,
    improvement,
    immediateWin,
    score:
      othersTotal*3+
      missing*5.5+
      improvement*4+
      (immediateWin?80:0)+
      cpuResourceKeepValue(
        player,
        resource,
        selectedGoal
      ),
  };
}

function cpuBestMonopolyResource(player){
  const goal=cpuChooseGoal(player);

  const results=RESOURCES.map(resource=>
    cpuMonopolyResourceScore(
      player,
      resource,
      goal
    )
  );

  results.sort((a,b)=>{
    if(Math.abs(b.score-a.score)>.001){
      return b.score-a.score;
    }
    return a.resource.localeCompare(b.resource);
  });

  return results[0]||null;
}

function cpuCanYearOfPlentyHelp(player){
  if(
    usableDevCount(
      player,
      "yearOfPlenty"
    )<=0
  ){
    return false;
  }

  const goal=cpuChooseGoal(player);

  if(!goal?.cost) return false;

  const missing=
    cpuResourceMissingCount(
      player,
      cpuGoalPlanCost(goal)
    );

  return missing>0 && missing<=2;
}

function cpuShouldPlayKnight(player){
  if(
    usableDevCount(
      player,
      "knight"
    )<=0
  ){
    return false;
  }

  if(robberHurtsPlayer(player)){
    return true;
  }

  const nextKnights=
    player.knightsPlayed+1;

  const maximumOpponentKnights=
    Math.max(
      0,
      ...game.players
        .filter(other=>other.id!==player.id)
        .map(other=>other.knightsPlayed||0)
    );

  if(
    nextKnights>=3 &&
    nextKnights>maximumOpponentKnights
  ){
    return true;
  }

  const leader=
    [...game.players]
      .filter(other=>other.id!==player.id)
      .sort(
        (a,b)=>
          publicVP(b)-publicVP(a)
      )[0];

  return (
    !!leader &&
    publicVP(leader)>=7 &&
    robberTargetScore(
      cpuBestRobberHexId(player.id),
      player.id
    )>6
  );
}

function cpuBestRobberHexId(playerId){
  const options=
    game.board.hexes.filter(
      hex=>hex.id!==game.robberHex
    );

  if(!options.length){
    return game.robberHex;
  }

  options.sort(
    (a,b)=>
      robberTargetScore(
        b,
        playerId
      )-
      robberTargetScore(
        a,
        playerId
      )
  );

  return options[0].id;
}

function cpuDiscardHalf(player,need){
  const actualNeed=
    Math.max(
      0,
      Math.min(
        Number(need)||0,
        totalResources(player)
      )
    );

  if(actualNeed<=0) return false;

  const goal=cpuChooseGoal(player);
  const stateBefore=cpuAnalysisStateSnapshot(player);
  const keepValues=Object.fromEntries(
    RESOURCES.map(resource=>[
      resource,
      cpuAnalysisRound(
        cpuResourceKeepValue(
          player,
          resource,
          goal
        )
      ),
    ])
  );
  const discardedByResource=Object.fromEntries(
    RESOURCES.map(resource=>[resource,0])
  );

  let left=actualNeed;

  while(left>0){
    const resource=
      cpuChooseDiscardResource(player);

    if(!resource) break;

    player.resources[resource]--;
    game.bank[resource]++;
    discardedByResource[resource]++;
    left--;
  }

  const discarded=
    actualNeed-left;

  cpuAnalysisRecordEvent(
    "discard_decision",
    player,
    {
      need:actualNeed,
      goal:goal?cpuAnalysisGoalSummary(player,goal):null,
      keepValues,
      discardedByResource,
      stateBefore,
      stateAfter:cpuAnalysisStateSnapshot(player),
    }
  );

  if(discarded>0){
    showResourceDelta(
      player.id,
      {unknown:-discarded},
      "7の破棄"
    );

    cpuAnalysisRecordAction(
      player,
      "discard_for_seven",
      {
        need:actualNeed,
        discarded,
        discardedByResource,
        keepValues,
      }
    );

    log(
      `${player.name}は資源を`+
      `${discarded}枚捨てました。`
    );
  }

  return discarded===actualNeed;
}


function clearCpuDiscardSchedule(){
  clearTimeout(cpuDiscardTimer);
  cpuDiscardTimer=null;
  cpuDiscardScheduledKey=null;
}

function scheduleCpuDiscard(
  player,
  need
){
  if(
    !player ||
    player.human ||
    !game ||
    game.phase!=="discard"
  ){
    return false;
  }

  if(
    ONLINE_MODE &&
    !isOnlineHost()
  ){
    return false;
  }

  const scheduledKey=[
    game.turnSerial,
    player.id,
    need,
    totalResources(player),
  ].join(":");

  if(
    cpuDiscardTimer &&
    cpuDiscardScheduledKey===scheduledKey
  ){
    return true;
  }

  clearCpuDiscardSchedule();
  cpuDiscardScheduledKey=scheduledKey;

  cpuDiscardTimer=setTimeout(()=>{
    cpuDiscardTimer=null;

    if(
      !game ||
      game.phase!=="discard" ||
      !Array.isArray(game.discardQueue) ||
      game.discardQueue[0]!==player.id
    ){
      cpuDiscardScheduledKey=null;
      return;
    }

    const currentPlayerById=
      playerById(player.id);

    if(
      !currentPlayerById ||
      currentPlayerById.human
    ){
      cpuDiscardScheduledKey=null;
      return;
    }

    const currentNeed=
      Math.floor(
        totalResources(
          currentPlayerById
        )/2
      );

    cpuDiscardHalf(
      currentPlayerById,
      currentNeed
    );

    game.discardQueue.shift();
    game.discardPlayerId=null;
    cpuDiscardScheduledKey=null;

    processDiscardQueue();
  },CPU_ACTION_DELAY_MS);

  return true;
}

function resumeCpuDiscardIfNeeded(){
  if(
    !game ||
    game.phase!=="discard" ||
    !Array.isArray(game.discardQueue) ||
    !game.discardQueue.length
  ){
    clearCpuDiscardSchedule();
    return false;
  }

  const player=
    playerById(
      game.discardQueue[0]
    );

  if(
    !player ||
    player.human
  ){
    return false;
  }

  const need=
    Math.floor(
      totalResources(player)/2
    );

  return scheduleCpuDiscard(
    player,
    need
  );
}

function openDiscardModal(player,need){
  discardSelection={playerId:player.id,need,selected:Object.fromEntries(RESOURCES.map(r=>[r,0]))};
  $("discardTitle").textContent=`${player.name}：資源を${need}枚捨てます`;
  $("discardGuide").textContent="資源をクリックすると1枚追加、左下の－で1枚戻せます。必要枚数を選んで確定してください。";
  $("discardModal").classList.remove("hidden");
  renderDiscardChoices();
}

function selectedDiscardCount(){
  return discardSelection ? RESOURCES.reduce((n,r)=>n+discardSelection.selected[r],0) : 0;
}

function changeDiscardChoice(resource,delta){
  if(!discardSelection) return;
  const player=playerById(discardSelection.playerId);
  const current=discardSelection.selected[resource];
  const total=selectedDiscardCount();
  if(delta>0){
    if(total>=discardSelection.need || current>=player.resources[resource]) return;
    discardSelection.selected[resource]++;
  }else if(current>0){
    discardSelection.selected[resource]--;
  }
  renderDiscardChoices();
}

function renderDiscardChoices(){
  if(!discardSelection) return;
  const player=playerById(discardSelection.playerId);
  $("discardChoices").innerHTML=RESOURCES.map(r=>{
    const selected=discardSelection.selected[r];
    return `<div class="discard-choice ${r} ${selected?"selected":""}" data-discard-add="${r}">
      <span class="discard-choice-icon">${RESOURCE_ICON[r]}</span>
      <span class="discard-choice-name">${RESOURCE_JA[r]}</span>
      <span class="discard-choice-stock">所持 ${player.resources[r]}枚</span>
      <span class="discard-choice-selected">選択 ${selected}枚</span>
      <button class="discard-minus" data-discard-minus="${r}" ${selected?"":"disabled"}>－</button>
      <span class="discard-plus-label">クリックで＋1</span>
    </div>`;
  }).join("");
  document.querySelectorAll("[data-discard-add]").forEach(el=>el.addEventListener("click",e=>{
    if(e.target.closest("[data-discard-minus]")) return;
    changeDiscardChoice(el.dataset.discardAdd,1);
  }));
  document.querySelectorAll("[data-discard-minus]").forEach(el=>el.addEventListener("click",e=>{
    e.stopPropagation(); changeDiscardChoice(el.dataset.discardMinus,-1);
  }));
  const count=selectedDiscardCount();
  $("discardCount").textContent=`選択 ${count} / ${discardSelection.need}枚`;
  $("discardConfirmBtn").disabled=count!==discardSelection.need;
}

function confirmDiscard(){
  if(!discardSelection || selectedDiscardCount()!==discardSelection.need) return;
  const player=playerById(discardSelection.playerId);
  if(!isLocalPlayer(player)) return;
  cpuAnalysisQueueHumanReceipt(
    player,
    "discard_on_seven",
    {
      need:discardSelection.need,
      selected:{...discardSelection.selected},
    }
  );
  const removed={};
  for(const r of RESOURCES){
    const n=discardSelection.selected[r];
    if(!n) continue;
    player.resources[r]-=n;
    game.bank[r]+=n;
    removed[r]=-n;
  }
  showResourceDelta(
    player.id,
    removed,
    "7の破棄",
    {
      privatePlayerIds:[player.id],
      publicDelta:{unknown:-discardSelection.need},
    }
  );
  log(`${player.name}は資源を${discardSelection.need}枚捨てました。`);
  discardSelection=null;
  hideDiscardModal();
  if(game.discardQueue[0]===player.id) game.discardQueue.shift();
  game.discardPlayerId=null;
  processDiscardQueue();
}

function processDiscardQueue(){
  if(!Array.isArray(game.discardQueue)) game.discardQueue=[];
  if(!game.discardQueue.length){
    game.discardPlayerId=null;
    beginRobberMove();
    return;
  }
  const player=playerById(game.discardQueue[0]);
  const need=Math.floor(totalResources(player)/2);
  game.phase="discard";
  game.discardPlayerId=player.id;
  render();

  if(!player.human){
    scheduleCpuDiscard(
      player,
      need
    );
  }else if(isLocalPlayer(player)){
    clearCpuDiscardSchedule();
    openDiscardModal(player,need);
  }
}

function handleSeven(playerId,afterResolve=null){
  game.robberMover=playerId;
  game.robberAfterKnight=false;
  game.pendingAfterRobber=typeof afterResolve==="function"?afterResolve:null;
  game.pendingCpuBuildAfterRobber=
    typeof afterResolve==="function" && !playerById(playerId).human;
  game.discardQueue=game.players.filter(p=>totalResources(p)>7).map(p=>p.id);
  game.discardPlayerId=null;
  if(game.discardQueue.length){
    game.phase="discard";
    log("7が出たため、8枚以上持っているプレイヤーは資源を半分捨てます。");
    processDiscardQueue();
  }else{
    beginRobberMove();
  }
}

function beginRobberMove(){
  game.phase="moveRobber";
  log(`${playerById(game.robberMover).name}が🐱を移動します。`);
  render();
  if(!playerById(game.robberMover).human && (!ONLINE_MODE || isOnlineHost())){
    setTimeout(()=>cpuMoveRobber(game.robberMover),CPU_ACTION_DELAY_MS);
  }
}

function robberVictimCandidates(hexId,playerId){
  const hex=game?.board?.hexes?.[hexId];
  if(!hex) return [];

  const victimIds=new Set();

  for(const vertexId of hex.corners){
    const building=
      game.board.vertices?.[vertexId]?.building;

    if(
      !building ||
      building.player===playerId
    ){
      continue;
    }

    const victim=playerById(building.player);

    if(
      victim &&
      totalResources(victim)>0
    ){
      victimIds.add(victim.id);
    }
  }

  return [...victimIds]
    .map(playerById)
    .filter(Boolean);
}

function canRobberStealFrom(
  playerId,
  victimId,
  hexId=game?.robberHex
){
  if(
    victimId===null ||
    victimId===undefined ||
    hexId===null ||
    hexId===undefined
  ){
    return false;
  }

  return robberVictimCandidates(
    hexId,
    playerId
  ).some(
    player=>player.id===victimId
  );
}

function finishRobberMove(playerId,victimId=null){
  if(victimId!==null){
    const mover=playerById(playerId);
    if(mover?.human && isLocalPlayer(mover)){
      cpuAnalysisQueueHumanReceipt(
        mover,
        "robber_victim",
        {hexId:game.robberHex??null,victimId}
      );
    }
    if(
      canRobberStealFrom(
        playerId,
        victimId,
        game.robberHex
      )
    ){
      stealRandom(playerId,victimId);
    }else{
      log(
        "盗賊に隣接していないプレイヤーからは"+
        "資源を奪えません。"
      );
      victimId=null;
    }
  }

  game.phase="turn";
  const continuation=game.pendingAfterRobber;
  const resumeCpuBuild=!!game.pendingCpuBuildAfterRobber;
  game.pendingAfterRobber=null;
  game.pendingCpuBuildAfterRobber=false;
  render();

  if(game.winner){
    cpuActionRunning=false;
    return;
  }

  if(typeof continuation==="function"){
    const mover=playerById(playerId);
    setTimeout(
      continuation,
      mover?.human ?280:CPU_ACTION_DELAY_MS
    );
  }else if(
    resumeCpuBuild &&
    game.current===playerId &&
    !playerById(playerId).human &&
    (!ONLINE_MODE || isOnlineHost())
  ){
    setTimeout(
      ()=>cpuBuildPhase(playerId,"fish"),
      CPU_ACTION_DELAY_MS
    );
  }
}

function moveRobberTo(hexId,playerId){
  if(hexId===game.robberHex) return false;
  const mover=playerById(playerId);
  if(mover?.human && isLocalPlayer(mover)){
    cpuAnalysisQueueHumanReceipt(
      mover,
      "move_robber",
      {fromHexId:game.robberHex??null,toHexId:hexId}
    );
  }
  game.robberHex=hexId;

  const candidates=
    robberVictimCandidates(
      hexId,
      playerId
    );

  if(
    candidates.length &&
    isLocalPlayer(playerById(playerId))
  ){
    game.phase="chooseVictim";
    render();

    const openVictimSelection=()=>{
      if(
        game.phase!=="chooseVictim" ||
        game.robberMover!==playerId
      ){
        return;
      }

      const currentCandidates=
        robberVictimCandidates(
          game.robberHex,
          playerId
        );

      if(!currentCandidates.length){
        finishRobberMove(playerId,null);
        return;
      }

      openChoiceModal({
        title:"資源を奪う相手",
        guide:
          "この土地に隣接するプレイヤーから、"+
          "資源をランダムに1枚奪います。",
        options:playerChoiceOptions(
          currentCandidates,
          player=>
            `資源カード `+
            `${totalResources(player)}枚`
        ),
        allowCancel:false,
        onSelect:victimId=>{
          confirmStealTarget(
            victimId,
            confirmedVictimId=>{
              if(
                game.phase!=="chooseVictim" ||
                game.robberMover!==playerId
              ){
                return;
              }

              if(
                !canRobberStealFrom(
                  playerId,
                  confirmedVictimId,
                  game.robberHex
                )
              ){
                log(
                  "そのプレイヤーは盗賊のいるタイルに"+
                  "隣接していません。"
                );
                openVictimSelection();
                return;
              }

              finishRobberMove(
                playerId,
                confirmedVictimId
              );
            },
            openVictimSelection
          );
        },
      });
    };

    openVictimSelection();
  }else{
    const victimId=
      candidates.length
        ?candidates[rand(candidates.length)].id
        :null;

    finishRobberMove(playerId,victimId);
  }

  return true;
}

function stealRandom(thiefId,victimId,reason="🐱"){
  const victim=playerById(victimId), thief=playerById(thiefId);
  const pool=[];
  RESOURCES.forEach(r=>{ for(let i=0;i<victim.resources[r];i++) pool.push(r); });
  if(!pool.length) return;
  const r=pool[rand(pool.length)];
  victim.resources[r]--;
  thief.resources[r]++;

  if(reason==="魚3匹"){
    queueAwardEvent(
      "fishSteal",
      thief.id,
      {
        targetPlayerId:victim.id,
        targetPlayerName:victim.name,
        playerLine:`${thief.name}が${victim.name}から`,
      }
    );
  }

  const privatePlayerIds=[thiefId,victimId];

  showResourceDelta(
    thiefId,
    {[r]:1},
    reason,
    {
      privatePlayerIds,
      publicDelta:{unknown:1},
    }
  );

  showResourceDelta(
    victimId,
    {[r]:-1},
    reason,
    {
      privatePlayerIds,
      publicDelta:{unknown:-1},
    }
  );

  log(`${thief.name}が${reason==="🐱"?"🐱で":"魚の効果で"}${victim.name}から資源を1枚奪いました。`);
}
function cpuMoveRobber(playerId){
  const player=playerById(playerId);
  const scoredHexes=game.board.hexes
    .filter(hex=>hex.id!==game.robberHex)
    .map(hex=>({
      hexId:hex.id,
      resource:hex.resource,
      number:hex.number??null,
      lakeNumbers:hex.lakeNumbers?[...hex.lakeNumbers]:null,
      score:robberTargetScore(hex,playerId),
    }))
    .sort((a,b)=>b.score-a.score);

  const bestHexId=
    scoredHexes[0]?.hexId??
    cpuBestRobberHexId(playerId);

  if(
    bestHexId===null ||
    bestHexId===undefined
  ){
    cpuAnalysisRecordEvent(
      "robber_decision",
      player,
      {
        selectedHexId:null,
        hexCandidates:scoredHexes,
        victimCandidates:[],
      }
    );
    finishRobberMove(
      playerId,
      null
    );
    return;
  }

  const candidates=
    robberVictimCandidates(
      bestHexId,
      playerId
    );

  const victimScores=candidates.map(victim=>({
    playerId:victim.id,
    name:victim.name,
    score:cpuVictimScore(victim,player),
    publicVP:publicVP(victim),
    resources:totalResources(victim),
    hasLongestRoad:!!victim.hasLongestRoad,
    hasLargestArmy:!!victim.hasLargestArmy,
  })).sort((a,b)=>b.score-a.score);

  const victim=
    cpuChooseVictimFromCandidates(
      candidates,
      playerId
    );

  cpuAnalysisRecordEvent(
    "robber_decision",
    player,
    {
      selectedHexId:bestHexId,
      selectedVictimId:victim?.id??null,
      hexCandidates:scoredHexes.slice(0,20).map((item,index)=>({
        rank:index+1,
        ...item,
        score:cpuAnalysisRound(item.score),
      })),
      victimCandidates:victimScores.map((item,index)=>({
        rank:index+1,
        ...item,
        score:cpuAnalysisRound(item.score),
      })),
      stateBefore:cpuAnalysisStateSnapshot(player),
    }
  );

  game.robberHex=bestHexId;

  cpuAnalysisRecordAction(
    player,
    "move_robber",
    {
      hexId:bestHexId,
      victimId:victim?.id??null,
      hexScore:cpuAnalysisRound(scoredHexes[0]?.score),
    }
  );

  finishRobberMove(
    playerId,
    victim?.id??null
  );
}


function robberTargetScore(h,playerId){
  if(
    typeof h==="number" ||
    typeof h==="string"
  ){
    h=game.board.hexes[h];
  }

  if(!h) return -9999;

  const thief=playerById(playerId);

  const productionWeight=
    h.number
      ?PIPS[h.number]||0
      :(h.lakeNumbers||[])
        .reduce(
          (sum,number)=>
            sum+(PIPS[number]||0),
          0
        )/2;

  let score=0;
  let opponentBuildings=0;

  for(const vertexId of h.corners){
    const building=
      game.board.vertices[vertexId]?.building;

    if(!building) continue;

    const owner=
      playerById(building.player);

    const strength=
      cpuBuildingMultiplier(
        building
      );

    if(building.player===playerId){
      score -=
        strength*
        (
          6+
          productionWeight*1.8
        );

      continue;
    }

    opponentBuildings+=strength;

    const threat=
      1+
      publicVP(owner)*.18+
      totalResources(owner)*.035+
      (
        owner.hasLongestRoad ||
        owner.hasLargestArmy
          ?0.35
          :0
      );

    score +=
      strength*
      productionWeight*
      threat;
  }

  const candidates=
    robberVictimCandidates(
      h.id,
      playerId
    );

  const bestVictim=
    cpuChooseVictimFromCandidates(
      candidates,
      playerId
    );

  if(bestVictim){
    score +=
      cpuVictimScore(
        bestVictim,
        thief
      )*.42;
  }

  if(opponentBuildings===0){
    score-=4.5;
  }

  return score+
    cpuStableTie(`robber:${h.id}:${playerId}`)*.02;
}

function setBuildMode(mode){
  const p=currentPlayer();
  if(!isLocalPlayer(p) || game.phase!=="turn" || !game.rolled || game.winner) return;
  if(p.builtThisTurn){
    log("このターンの建設は既に行っています。");
    return;
  }
  if(mode==="road"){
    if(p.pieces.road<=0 || !hasCost(p,COST.road)){ log("街道を建てる資源または駒が足りません。"); return; }
  } else if(mode==="settlement"){
    if(p.pieces.settlement<=0 || !hasCost(p,COST.settlement)){ log("開拓地を建てる資源または駒が足りません。"); return; }
  } else if(mode==="city"){
    if(p.pieces.city<=0 || !hasCost(p,COST.city)){ log("都市を建てる資源または駒が足りません。"); return; }
  } else if(mode==="dev"){
    if(!game.devDeck.length){
      log("発展カードを買えません。発展カードの山札が空です。");
      return;
    }
    if(!hasCost(p,COST.dev)){
      log(`発展カードを買えません。不足：${missingCostText(p,COST.dev)}`);
      return;
    }
    cpuAnalysisQueueHumanReceipt(p,"buy_development",{});
    buyDev(p.id); checkVictory(); render(); return;
  }
  game.buildMode=mode; render();
}

function normalClickVertex(vertexId){
  const p=currentPlayer();

  if(
    !isLocalPlayer(p) ||
    game.phase!=="turn" ||
    !game.rolled
  ){
    return;
  }

  if(game.buildMode==="settlement"){
    if(!canPlaceSettlement(p.id,vertexId,false)){
      log("そこには開拓地を建てられません。");
      return;
    }

    requestPlacementConfirmation({
      kind:"settlement",
      targetId:vertexId,
      itemName:"開拓地",
      guide:"開拓地をこの交差点に建てます。",
      onConfirm:()=>{
        const player=currentPlayer();

        if(
          !isLocalPlayer(player) ||
          game.phase!=="turn" ||
          game.buildMode!=="settlement" ||
          !canPlaceSettlement(
            player.id,
            vertexId,
            false
          )
        ){
          log("その場所には建てられなくなりました。");
          render();
          return;
        }

        cpuAnalysisQueueHumanReceipt(
          player,
          "build_settlement",
          {vertexId}
        );

        payCost(
          player,
          COST.settlement,
          "開拓地建設"
        );
        placeSettlement(
          player.id,
          vertexId,
          false
        );

        player.builtThisTurn=true;
        game.buildMode=null;

        log("あなたが開拓地を建てました。");
        updateAwards();
        checkVictory();
        render();
      },
    });
    return;
  }

  if(game.buildMode==="city"){
    if(!canUpgradeCity(p.id,vertexId)){
      log("自分の開拓地を選んでください。");
      return;
    }

    requestPlacementConfirmation({
      kind:"city",
      targetId:vertexId,
      itemName:"都市",
      guide:"この開拓地を都市へ発展させます。",
      onConfirm:()=>{
        const player=currentPlayer();

        if(
          !isLocalPlayer(player) ||
          game.phase!=="turn" ||
          game.buildMode!=="city" ||
          !canUpgradeCity(
            player.id,
            vertexId
          )
        ){
          log("その場所には建てられなくなりました。");
          render();
          return;
        }

        cpuAnalysisQueueHumanReceipt(
          player,
          "build_city",
          {vertexId}
        );
        placeCity(player.id,vertexId);
        player.builtThisTurn=true;
        game.buildMode=null;

        log("あなたが都市を建てました。");
        updateAwards();
        checkVictory();
        render();
      },
    });
  }
}
function normalClickEdge(edgeId){
  const p=currentPlayer();

  if(
    !isLocalPlayer(p) ||
    game.phase!=="turn"
  ){
    return;
  }

  const free=game.freeRoads>0;

  if(game.buildMode!=="road" && !free) return;

  if(!canPlaceRoad(p.id,edgeId)){
    log("そこには街道を建てられません。");
    return;
  }

  if(!free && !game.rolled) return;

  requestPlacementConfirmation({
    kind:"road",
    targetId:edgeId,
    itemName:"街道",
    guide:
      free
        ?"無料の街道をこの辺に置きます。"
        :"街道をこの辺に建てます。",
    onConfirm:()=>{
      const player=currentPlayer();
      const stillFree=game.freeRoads>0;

      if(
        !isLocalPlayer(player) ||
        game.phase!=="turn" ||
        (
          game.buildMode!=="road" &&
          !stillFree
        ) ||
        !canPlaceRoad(player.id,edgeId)
      ){
        log("その場所には建てられなくなりました。");
        render();
        return;
      }

      cpuAnalysisQueueHumanReceipt(
        player,
        stillFree?"build_road_free":"build_road",
        {edgeId,free:stillFree}
      );

      placeRoad(
        player.id,
        edgeId,
        stillFree
      );

      log(
        `あなたが街道を建てました`+
        `${stillFree?"（無料）":""}。`
      );

      if(stillFree){
        game.freeRoads--;

        if(game.freeRoads===0){
          game.buildMode=null;
        }
      }else{
        player.builtThisTurn=true;
        game.buildMode=null;
      }

      checkVictory();
      render();
    },
  });
}

function getTradeRate(player,resource){
  let rate=4;
  const buildings=[...player.settlements,...player.cities];
  for(const vid of buildings){
    for(const eid of game.board.vertices[vid].edges){
      const h=game.board.edges[eid].harbor;
      if(h==="3:1") rate=Math.min(rate,3);
      if(h===resource) rate=Math.min(rate,2);
    }
  }
  return rate;
}
function updateTradeRate(){
  if(!game) return;
  const r=$("tradeGive").value;
  const rate=getTradeRate(localPlayer(),r);
  $("tradeRate").textContent=`${rate}枚 → 1枚`;
}

function bankTrade(){
  const p=currentPlayer();
  if(!isLocalPlayer(p) || game.phase!=="turn" || !game.rolled) return;
  const give=$("tradeGive").value, get=$("tradeGet").value;
  if(give===get){ log("別の資源を選んでください。"); return; }
  const rate=getTradeRate(p,give);
  if(p.resources[give]<rate){ log(`${RESOURCE_JA[give]}が${rate}枚必要です。`); return; }
  if(game.bank[get]<1){ log("銀行に希望資源がありません。"); return; }
  cpuAnalysisQueueHumanReceipt(
    p,
    "bank_trade",
    {give,get,rate}
  );
  p.resources[give]-=rate; game.bank[give]+=rate;
  p.resources[get]++; game.bank[get]--;
  showResourceDelta(p.id,{[give]:-rate,[get]:1},"銀行・港交易");
  log(`${p.name}が${RESOURCE_JA[give]}${rate}枚を${RESOURCE_JA[get]}1枚に交換しました。`);
  render();
}

function emptyResourceCounts(){
  return Object.fromEntries(RESOURCES.map(resource=>[resource,0]));
}

function openPlayerTradeModal(){
  const player=currentPlayer();
  if(!isLocalPlayer(player) || game.phase!=="turn" || !game.rolled || game.winner) return;
  if(game.pendingTrade){
    log("現在の交易提案への回答を待っています。");
    return;
  }
  const targets=game.players.filter(other=>other.id!==player.id);
  if(!targets.length) return;
  tradeDraft={
    targetId:targets[0].id,
    give:emptyResourceCounts(),
    get:emptyResourceCounts(),
  };
  renderTradeModal();
  $("tradeModal").classList.remove("hidden");
}

function closeTradeModal(){
  const modal=$("tradeModal");
  if(modal) modal.classList.add("hidden");
  tradeDraft=null;
}

function tradeResourceText(counts){
  const items=RESOURCES
    .filter(resource=>counts[resource]>0)
    .map(resource=>`${RESOURCE_ICON[resource]}${RESOURCE_JA[resource]}×${counts[resource]}`);
  return items.length?items.join("、"):"なし";
}

function changeTradeQuantity(side,resource,delta){
  if(!tradeDraft) return;

  const player=localPlayer();
  const target=playerById(tradeDraft.targetId);
  if(!player || !target) return;

  const counts=tradeDraft[side];
  const opposite=tradeDraft[side==="give"?"get":"give"];
  const maximum=side==="give"
    ?Math.max(0,player.resources[resource])
    :TRADE_REQUEST_MAX;

  counts[resource]=Math.max(
    0,
    Math.min(maximum,counts[resource]+delta)
  );

  if(counts[resource]>0){
    opposite[resource]=0;
  }

  renderTradeModal();
}

function renderTradeResourceEditor(containerId,side,owner){
  const counts=tradeDraft[side];
  const isRequestSide=side==="get";

  $(containerId).innerHTML=RESOURCES.map(resource=>{
    const maximum=isRequestSide
      ?TRADE_REQUEST_MAX
      :Math.max(0,owner.resources[resource]);

    const stockText=isRequestSide
      ?"相手の所持数は非公開"
      :`所持 ${Math.max(0,owner.resources[resource])}枚`;

    return `<div class="trade-resource-line">
      <div>
        <span class="trade-resource-name">${RESOURCE_ICON[resource]} ${RESOURCE_JA[resource]}</span>
        <span class="trade-resource-stock">${stockText}</span>
      </div>
      <button
        class="trade-qty-button"
        data-trade-side="${side}"
        data-trade-resource="${resource}"
        data-trade-delta="-1"
        ${counts[resource]<=0?"disabled":""}
      >−</button>
      <span class="trade-resource-count">${counts[resource]}</span>
      <button
        class="trade-qty-button"
        data-trade-side="${side}"
        data-trade-resource="${resource}"
        data-trade-delta="1"
        ${counts[resource]>=maximum?"disabled":""}
      >＋</button>
    </div>`;
  }).join("");
}

function renderTradeModal(){
  if(!tradeDraft) return;
  const player=localPlayer();
  const targets=game.players.filter(other=>other.id!==player.id);
  if(!targets.some(target=>target.id===tradeDraft.targetId)) tradeDraft.targetId=targets[0]?.id??null;
  const target=playerById(tradeDraft.targetId);

  $("tradePlayerChoices").innerHTML=targets.map(other=>`
    <button class="trade-player-choice ${other.id===tradeDraft.targetId?"selected":""}" data-trade-player="${other.id}">
      <span class="player-dot" style="background:${other.color}"></span>
      <span>${other.name}<br><small>資源カード合計 ${Math.max(0,totalResources(other))}枚（内訳非公開）</small></span>
    </button>
  `).join("");

  if(!target) return;
  renderTradeResourceEditor("tradeOfferEditor","give",player);
  renderTradeResourceEditor("tradeRequestEditor","get",target);

  const giveTotal=RESOURCES.reduce((sum,r)=>sum+tradeDraft.give[r],0);
  const getTotal=RESOURCES.reduce((sum,r)=>sum+tradeDraft.get[r],0);
  $("tradeProposalSummary").innerHTML=`
    <strong>${target.name}</strong>へ提案<br>
    渡す：${tradeResourceText(tradeDraft.give)}<br>
    貰う：${tradeResourceText(tradeDraft.get)}
  `;
  $("tradeConfirmBtn").disabled=!target || giveTotal===0 || getTotal===0;

  document.querySelectorAll("[data-trade-player]").forEach(button=>{
    button.addEventListener("click",()=>{
      tradeDraft.targetId=Number(button.dataset.tradePlayer);
      tradeDraft.get=emptyResourceCounts();
      renderTradeModal();
    });
  });
  document.querySelectorAll("[data-trade-delta]").forEach(button=>{
    button.addEventListener("click",()=>changeTradeQuantity(
      button.dataset.tradeSide,
      button.dataset.tradeResource,
      Number(button.dataset.tradeDelta)
    ));
  });
}

function cpuTradeResourceValue(player,resource){
  const goals=[COST.city,COST.settlement,COST.road,COST.dev];
  let value=1;
  if(player.resources[resource]===0) value+=0.25;
  for(const goal of goals){
    const need=Math.max(0,(goal[resource]||0)-player.resources[resource]);
    value+=need*0.18;
  }
  if(player.resources[resource]>=4) value-=0.12;
  return Math.max(.55,value);
}

function cpuCanImmediateWinWithResources(
  player,
  resources
){
  const needed=
    victoryTarget(player)-
    totalVP(player);

  if(needed<=0) return true;

  const canPay=cost=>
    RESOURCES.every(resource=>
      (resources[resource]||0)>=
      (cost[resource]||0)
    );

  if(needed<=1){
    if(
      player.pieces.city>0 &&
      player.settlements.some(vertexId=>
        canUpgradeCity(
          player.id,
          vertexId
        )
      ) &&
      canPay(COST.city)
    ){
      return true;
    }

    if(
      player.pieces.settlement>0 &&
      Object.keys(game.board.vertices)
        .some(vertexId=>
          canPlaceSettlement(
            player.id,
            vertexId,
            false
          )
        ) &&
      canPay(COST.settlement)
    ){
      return true;
    }
  }

  if(
    needed<=2 &&
    player.pieces.road>0 &&
    canPay(COST.road)
  ){
    const roadPlan=
      cpuBestRoadSequence(
        player,
        1
      );

    if(
      roadPlan?.awardGain>=needed
    ){
      return true;
    }
  }

  return false;
}

function cpuAcceptTrade(
  cpu,
  give,
  get,
  proposer=null
){
  for(const resource of RESOURCES){
    if(
      (get[resource]||0)>
      cpu.resources[resource]
    ){
      return false;
    }
  }

  const goal=
    cpuChooseGoal(cpu);

  const receivedValue=
    RESOURCES.reduce(
      (sum,resource)=>
        sum+
        (give[resource]||0)*
        cpuResourceKeepValue(
          cpu,
          resource,
          goal
        ),
      0
    );

  const paidValue=
    RESOURCES.reduce(
      (sum,resource)=>
        sum+
        (get[resource]||0)*
        cpuResourceKeepValue(
          cpu,
          resource,
          goal
        ),
      0
    );

  const delta={};

  for(const resource of RESOURCES){
    delta[resource]=
      (give[resource]||0)-
      (get[resource]||0);
  }

  const simulated=
    cpuSimulatedResources(
      cpu,
      delta
    );

  const ownImmediateWin=
    cpuCanImmediateWinWithResources(
      cpu,
      simulated
    );

  const beforeDistance=
    cpuGoalDistance(
      cpu,
      goal
    );

  const afterDistance=
    cpuGoalDistance(
      cpu,
      goal,
      simulated
    );

  const goalImprovement=
    beforeDistance-
    afterDistance;

  let leaderTax=0;

  if(proposer && proposer.id!==cpu.id){
    const proposerPoints=
      publicVP(proposer);
    const cpuPoints=
      publicVP(cpu);

    /*
      9点の相手とは、自分もこの交換で即勝利できる場合を除き
      原則交易しない。勝利目前の相手へ最後の1枚を渡す事故を防ぐ。
    */
    if(
      proposerPoints>=9 &&
      proposerPoints>=cpuPoints &&
      !ownImmediateWin
    ){
      return false;
    }

    if(
      proposerPoints>=9 &&
      proposerPoints>=cpuPoints
    ){
      leaderTax=.52;
    }else if(
      proposerPoints>=8 &&
      proposerPoints>cpuPoints
    ){
      leaderTax=.30;
    }else if(
      proposerPoints>=7 &&
      proposerPoints>cpuPoints
    ){
      leaderTax=.13;
    }
  }

  if(
    goalImprovement>=1.25 &&
    receivedValue>=
      paidValue*(.86+leaderTax)
  ){
    return true;
  }

  if(goalImprovement<-.35){
    return (
      receivedValue>=
      paidValue*(1.38+leaderTax)
    );
  }

  return (
    receivedValue>=
    paidValue*(1.08+leaderTax)
  );
}

function cpuTryPlayerTrade(player){
  if(
    player.cpuTradeTurnSerial===
    game.turnSerial
  ){
    return false;
  }

  player.cpuTradeTurnSerial=
    game.turnSerial;

  const goal=
    cpuChooseGoal(player);

  if(!goal?.cost){
    cpuAnalysisRecordEvent(
      "player_trade_decision",
      player,
      {reason:"no_goal",selected:null,candidates:[]}
    );
    return false;
  }

  const beforeDistance=
    cpuGoalDistance(
      player,
      goal
    );

  if(beforeDistance<=0){
    cpuAnalysisRecordEvent(
      "player_trade_decision",
      player,
      {
        reason:"goal_already_complete",
        goal:cpuAnalysisGoalSummary(player,goal),
        selected:null,
        candidates:[],
      }
    );
    return false;
  }

  const wanted=
    cpuGoalMissingResources(
      player,
      goal
    );

  if(!wanted.length){
    cpuAnalysisRecordEvent(
      "player_trade_decision",
      player,
      {
        reason:"no_missing_resource",
        goal:cpuAnalysisGoalSummary(player,goal),
        selected:null,
        candidates:[],
      }
    );
    return false;
  }

  const candidates=[];
  const rejected=[];

  for(const wantedItem of wanted){
    const receive=
      wantedItem.resource;

    for(const give of RESOURCES){
      if(give===receive) continue;

      const goalNeed=
        cpuGoalPlanCost(goal)[give]||0;

      const surplus=
        Math.max(
          0,
          player.resources[give]-
          goalNeed
        );

      const offerAmounts=[];

      if(player.resources[give]>=1){
        offerAmounts.push(1);
      }

      if(
        player.resources[give]>=2 &&
        surplus>=2
      ){
        offerAmounts.push(2);
      }

      for(const offerAmount of offerAmounts){
        const giveBundle=
          emptyResourceCounts();

        const getBundle=
          emptyResourceCounts();

        giveBundle[give]=offerAmount;
        getBundle[receive]=1;

        const simulated=
          cpuSimulatedResources(
            player,
            {
              [give]:-offerAmount,
              [receive]:1,
            }
          );

        const afterDistance=
          cpuGoalDistance(
            player,
            goal,
            simulated
          );

        const improvement=
          beforeDistance-
          afterDistance;

        if(improvement<=.05){
          continue;
        }

        for(const target of game.players){
          if(
            target.id===player.id ||
            target.human ||
            target.resources[receive]<1
          ){
            continue;
          }

          const accepted=
            cpuAcceptTrade(
              target,
              giveBundle,
              getBundle,
              player
            );

          if(!accepted){
            rejected.push({
              targetId:target.id,
              targetName:target.name,
              give,
              receive,
              offerAmount,
              improvement,
              reason:"target_rejected",
            });
            continue;
          }

          const targetPoints=
            publicVP(target);

          const playerPoints=
            publicVP(player);

          const ownImmediateWin=
            cpuCanImmediateWinWithResources(
              player,
              simulated
            );

          if(
            targetPoints>=9 &&
            targetPoints>=playerPoints &&
            !ownImmediateWin
          ){
            rejected.push({
              targetId:target.id,
              targetName:target.name,
              give,
              receive,
              offerAmount,
              improvement,
              reason:"leader_at_9",
            });
            continue;
          }

          const leaderPenalty=
            targetPoints>=9 &&
            targetPoints>=playerPoints
              ?40
              :targetPoints>=8 &&
                targetPoints>playerPoints
                ?18
                :targetPoints>=7 &&
                  targetPoints>playerPoints
                  ?7
                  :0;

          candidates.push({
            target,
            targetId:target.id,
            targetName:target.name,
            giveBundle,
            getBundle,
            giveResource:give,
            receiveResource:receive,
            offerAmount,
            beforeDistance,
            afterDistance,
            improvement,
            targetPoints,
            playerPoints,
            leaderPenalty,
            ownImmediateWin,
            score:
              improvement*12-
              offerAmount*1.5-
              leaderPenalty,
          });
        }
      }
    }
  }

  candidates.sort(
    (a,b)=>b.score-a.score
  );

  const best=candidates[0]||null;

  cpuAnalysisRecordEvent(
    "player_trade_decision",
    player,
    {
      reason:best?"selected_best_viable":"no_viable_trade",
      goal:cpuAnalysisGoalSummary(player,goal),
      wanted:cpuAnalysisClone(wanted),
      selected:best?{
        targetId:best.targetId,
        targetName:best.targetName,
        giveBundle:cpuAnalysisClone(best.giveBundle),
        getBundle:cpuAnalysisClone(best.getBundle),
        improvement:cpuAnalysisRound(best.improvement),
        leaderPenalty:best.leaderPenalty,
        ownImmediateWin:best.ownImmediateWin,
        score:cpuAnalysisRound(best.score),
      }:null,
      candidates:candidates.slice(0,20).map((candidate,index)=>({
        rank:index+1,
        targetId:candidate.targetId,
        targetName:candidate.targetName,
        giveBundle:cpuAnalysisClone(candidate.giveBundle),
        getBundle:cpuAnalysisClone(candidate.getBundle),
        improvement:cpuAnalysisRound(candidate.improvement),
        beforeDistance:cpuAnalysisRound(candidate.beforeDistance),
        afterDistance:cpuAnalysisRound(candidate.afterDistance),
        leaderPenalty:candidate.leaderPenalty,
        ownImmediateWin:candidate.ownImmediateWin,
        score:cpuAnalysisRound(candidate.score),
      })),
      rejected:rejected.slice(0,30).map(item=>({
        ...item,
        improvement:cpuAnalysisRound(item.improvement),
      })),
      stateBefore:cpuAnalysisStateSnapshot(player),
    }
  );

  if(!best){
    return false;
  }

  const completed=
    executePlayerTrade(
      best.target,
      best.giveBundle,
      best.getBundle,
      player,
      `cpu-trade-${game.turnSerial}-`+
      `${player.id}-`+
      `${Date.now()}`
    );

  if(completed){
    cpuAnalysisRecordAction(
      player,
      "player_trade",
      {
        targetId:best.targetId,
        targetName:best.targetName,
        giveBundle:cpuAnalysisClone(best.giveBundle),
        getBundle:cpuAnalysisClone(best.getBundle),
        score:cpuAnalysisRound(best.score),
        improvement:cpuAnalysisRound(best.improvement),
        goalKey:cpuGoalKey(goal),
      }
    );
    log(
      `${player.name}が`+
      `${best.target.name}と`+
      "CPU交易を行いました。"
    );
  }

  return completed;
}


function executePlayerTrade(
  target,
  give,
  get,
  player=localPlayer(),
  tradeId=null
){
  enforceResourceIntegrity();

  if(tradeId && tradeWasResolved(tradeId)){
    return false;
  }

  if(!canExecutePlayerTrade(player,target,give,get)){
    return false;
  }

  if(tradeId){
    rememberResolvedTrade(tradeId);
  }

  const playerDelta={};
  const targetDelta={};

  for(const resource of RESOURCES){
    const offered=give[resource]||0;
    const requested=get[resource]||0;

    if(offered>0){
      player.resources[resource]-=offered;
      target.resources[resource]+=offered;
      playerDelta[resource]=(playerDelta[resource]||0)-offered;
      targetDelta[resource]=(targetDelta[resource]||0)+offered;
    }

    if(requested>0){
      target.resources[resource]-=requested;
      player.resources[resource]+=requested;
      targetDelta[resource]=(targetDelta[resource]||0)-requested;
      playerDelta[resource]=(playerDelta[resource]||0)+requested;
    }
  }

  enforceResourceIntegrity();

  showResourceDelta(
    player.id,
    playerDelta,
    "プレイヤー交易"
  );
  showResourceDelta(
    target.id,
    targetDelta,
    "プレイヤー交易"
  );

  log(
    `${target.name}が交易を承諾しました。`+
    `渡した資源：${tradeResourceText(give)}／`+
    `受け取った資源：${tradeResourceText(get)}`
  );

  return true;
}

function submitPlayerTrade(){
  if(!tradeDraft) return;
  const player=localPlayer();
  const target=playerById(tradeDraft.targetId);
  if(!target) return;

  for(const resource of RESOURCES){
    if(tradeDraft.give[resource]>player.resources[resource]){
      log("渡す資源が不足しています。");
      renderTradeModal();
      return;
    }
  }

  const give=deepClone(tradeDraft.give);
  const get=deepClone(tradeDraft.get);
  cpuAnalysisQueueHumanReceipt(
    player,
    "player_trade_proposal",
    {
      targetId:target.id,
      targetName:target.name,
      give,
      get,
    }
  );
  closeTradeModal();

  if(ONLINE_MODE && target.human){
    game.pendingTrade={
      id:`${Date.now()}-${Math.random().toString(36).slice(2)}`,
      fromId:player.id,
      toId:target.id,
      give,
      get,
    };
    log(`${target.name}へ交易を提案しました。回答を待っています。`);
    render();
    return;
  }

  const cpuWantedToAccept=cpuAcceptTrade(
    target,
    give,
    get,
    player
  );
  const accepted=cpuWantedToAccept &&
    executePlayerTrade(target,give,get,player);

  if(!accepted){
    log(`${target.name}が交易を断りました。`);
  }

  render();

  openChoiceModal({
    title:`${target.name}の回答`,
    guide:accepted
      ? `YES：${target.name}が交易を承諾しました。`
      : `NO：${target.name}が交易を断りました。`,
    options:[{
      value:true,
      label:accepted?"YES":"NO",
      icon:accepted?"✓":"×",
      className:accepted?"yes":"no",
    }],
    allowCancel:false,
    onSelect:()=>render(),
  });
}

function cpuTradeProposal(){
  openPlayerTradeModal();
}

function fishTotal(player){ return player.fishTokens.reduce((a,b)=>a+b,0); }
function selectedFishTotal(){
  if(!game?.fishermen) return 0;
  const p=localPlayer();
  return game.selectedFishIndices.reduce((sum,i)=>sum+(p.fishTokens[i]||0),0);
}
function toggleFishToken(index){
  if(!game.fishermen || !isLocalTurn() || game.phase!=="turn" || game.freeRoads>0) return;
  const pos=game.selectedFishIndices.indexOf(index);
  if(pos>=0) game.selectedFishIndices.splice(pos,1); else game.selectedFishIndices.push(index);
  renderFishPanel();
}
function findFishPayment(tokens,cost){
  let best=null;
  const n=tokens.length;
  for(let mask=1;mask<(1<<n);mask++){
    const indices=[]; let total=0;
    for(let i=0;i<n;i++) if(mask&(1<<i)){ indices.push(i); total+=tokens[i]; }
    if(total<cost) continue;
    if(!best || total<best.total || (total===best.total && indices.length<best.indices.length)) best={indices,total};
  }
  return best;
}
function getHumanFishPayment(cost){
  const p=localPlayer();
  const selected=[...game.selectedFishIndices].filter(i=>i>=0&&i<p.fishTokens.length);
  const total=selected.reduce((s,i)=>s+p.fishTokens[i],0);
  if(selected.length) return total>=cost?{indices:selected,total}:null;
  return findFishPayment(p.fishTokens,cost);
}
function spendFish(player,indices,cost,reason){
  const sorted=[...indices].sort((a,b)=>b-a);
  let paid=0;
  for(const i of sorted){
    const [value]=player.fishTokens.splice(i,1);
    if(value){ paid+=value; game.fishDiscard.push(value); }
  }
  if(isLocalPlayer(player)) game.selectedFishIndices=[];
  log(`${player.name}が魚を${paid}匹分支払いました${paid>cost?`（超過${paid-cost}匹）`:""}：${reason}`);
  return paid>=cost;
}
function chooseVictim(playerId){
  const candidates=
    game.players.filter(
      player=>
        player.id!==playerId &&
        totalResources(player)>0
    );

  if(!candidates.length) return null;

  const player=playerById(playerId);

  if(!isLocalPlayer(player)){
    return cpuChooseVictimFromCandidates(
      candidates,
      playerId
    )?.id??null;
  }

  return candidates;
}

function executeFishAction(action,target,payment){
  const p=currentPlayer(),cost=FISH_ACTION_COST[action];
  if(p?.human && isLocalPlayer(p)){
    cpuAnalysisQueueHumanReceipt(
      p,
      "fish_action",
      {
        action,
        target:cpuAnalysisClone(target),
        cost,
        paymentIndices:[...(payment.indices||[])],
        paymentTotal:payment.total??cost,
      }
    );
  }
  spendFish(p,payment.indices,cost,{
    removeRobber:"🐱を盤外へ",
    steal:"資源強奪",
    resource:"資源獲得",
    road:"無料街道",
    dev:"無料発展カード",
  }[action]);
  if(action==="removeRobber"){
    game.robberHex=null;
    queueAwardEvent("fishRemoveRobber",p.id);
    log("🐱を盤外へ追い出しました。");
  }else if(action==="steal"){
    stealRandom(p.id,target,"魚3匹");
  }else if(action==="resource"){
    const got=gainResource(p,target,1);
    showResourceDelta(p.id,{[target]:got},"魚4匹");
  }else if(action==="road"){
    game.freeRoads+=1;
    game.buildMode="road";
    log("無料で置く街道の場所を選んでください。");
  }else if(action==="dev"){
    grantFreeDevelopmentCard(p,"魚7匹");
  }
  checkVictory();
  render();
}

function fishActionConfirmationText(action,target,cost,payment){
  let effectText="漁師の効果を使用します。";

  if(action==="removeRobber"){
    effectText="🐱を盤外へ追い出します。";
  }else if(action==="steal"){
    const victim=playerById(target);
    effectText=
      `${victim?.name||"選択した相手"}から`+
      "資源をランダムに1枚奪います。";
  }else if(action==="resource"){
    effectText=
      `${RESOURCE_JA[target]||"選択した資源"}を`+
      "銀行から1枚受け取ります。";
  }else if(action==="road"){
    effectText=
      "無料で街道を1本建設できる状態にします。";
  }else if(action==="dev"){
    effectText=
      "発展カードを無料で1枚獲得します。";
  }

  const paymentText=
    payment.total>cost
      ?(
        `魚チップ${payment.total}匹分を使います。`+
        `必要数は${cost}匹なので、`+
        `超過した${payment.total-cost}匹分は戻りません。`
      )
      :`魚チップ${cost}匹分を使います。`;

  return `${effectText}\n${paymentText}`;
}

function fishActionStillValid(action,target){
  const p=currentPlayer();

  if(
    !p ||
    !isLocalPlayer(p) ||
    game.phase!=="turn" ||
    game.winner ||
    game.freeRoads>0
  ){
    return false;
  }

  if(
    action==="removeRobber" &&
    game.robberHex===null
  ){
    return false;
  }

  if(action==="steal"){
    const victim=playerById(target);

    if(
      !victim ||
      victim.id===p.id ||
      totalResources(victim)<=0
    ){
      return false;
    }
  }

  if(
    action==="resource" &&
    (
      !RESOURCES.includes(target) ||
      game.bank[target]<=0
    )
  ){
    return false;
  }

  if(
    action==="road" &&
    (
      p.pieces.road<=0 ||
      !Object.keys(game.board.edges).some(
        edgeId=>canPlaceRoad(p.id,edgeId)
      )
    )
  ){
    return false;
  }

  if(
    action==="dev" &&
    !game.devDeck.length
  ){
    return false;
  }

  return true;
}

function confirmFishAction(action,target=null){
  const p=currentPlayer();
  const cost=FISH_ACTION_COST[action];
  const payment=getHumanFishPayment(cost);

  if(!payment){
    if(game.selectedFishIndices.length){
      log(
        `選択中の魚は${selectedFishTotal()}匹分です。`+
        `${cost}匹分以上を選んでください。`
      );
    }else{
      log(
        `${cost}匹分を支払える魚チップの`+
        "組み合わせがありません。"
      );
    }
    return;
  }

  const actionNames={
    removeRobber:"魚2匹：盗賊を追い払う",
    steal:"魚3匹：資源を奪う",
    resource:"魚4匹：好きな資源",
    road:"魚5匹：無料街道",
    dev:"魚7匹：無料発展",
  };

  openChoiceModal({
    title:"この漁師効果を発動していいですか？",
    guide:
      `${actionNames[action]||"漁師効果"}\n`+
      fishActionConfirmationText(
        action,
        target,
        cost,
        payment
      ),
    allowCancel:false,
    options:[
      {
        value:true,
        label:"はい",
        icon:"✓",
        className:"yes",
        sub:"魚チップを消費して発動",
      },
      {
        value:false,
        label:"いいえ",
        icon:"×",
        className:"no",
        sub:"発動せずに戻る",
      },
    ],
    onSelect:confirmed=>{
      if(!confirmed){
        renderFishPanel();
        return;
      }

      if(!fishActionStillValid(action,target)){
        log(
          "状況が変わったため、"+
          "この漁師効果は発動できませんでした。"
        );
        render();
        return;
      }

      const currentPayment=
        getHumanFishPayment(cost);

      if(!currentPayment){
        log(
          "魚チップが不足したため、"+
          "この漁師効果は発動できませんでした。"
        );
        render();
        return;
      }

      executeFishAction(
        action,
        target,
        currentPayment
      );
    },
  });
}

function performFishAction(action){
  if(!game.fishermen || game.winner || game.phase!=="turn" || !isLocalTurn() || game.freeRoads>0) return;
  const p=currentPlayer();
  if(action==="removeRobber" && game.robberHex===null){
    log("🐱はすでに盤外です。");
    return;
  }
  if(action==="road" && (p.pieces.road<=0 || !Object.keys(game.board.edges).some(e=>canPlaceRoad(p.id,e)))){
    log("無料街道を置ける場所または駒がありません。");
    return;
  }
  if(action==="dev" && !game.devDeck.length){
    log("発展カードの山札がありません。");
    return;
  }
  if(action==="steal"){
    const openFishVictimSelection=()=>{
      const currentPlayerNow=currentPlayer();

      if(
        !currentPlayerNow ||
        !isLocalPlayer(currentPlayerNow) ||
        game.phase!=="turn"
      ){
        return;
      }

      const candidates=
        chooseVictim(currentPlayerNow.id);

      if(!candidates?.length){
        log("資源を持つ相手がいません。");
        return;
      }

      openChoiceModal({
        title:"魚3匹：資源を奪う",
        guide:
          "資源をランダムに1枚奪う"+
          "相手を選択してください。",
        options:playerChoiceOptions(
          candidates,
          player=>
            `資源カード `+
            `${totalResources(player)}枚`
        ),
        onSelect:targetId=>{
          confirmStealTarget(
            targetId,
            confirmedTargetId=>{
              if(
                game.phase!=="turn" ||
                !isLocalTurn()
              ){
                return;
              }

              confirmFishAction(
                action,
                confirmedTargetId
              );
            },
            openFishVictimSelection
          );
        },
        allowCancel:true,
      });
    };

    openFishVictimSelection();
    return;
  }
  if(action==="resource"){
    openResourceChoice(
      "魚4匹：好きな資源",
      "銀行から受け取る資源を選択してください。",
      resource=>confirmFishAction(action,resource),
      {filter:resource=>game.bank[resource]>0}
    );
    return;
  }
  confirmFishAction(action,null);
}

function publicVP(player){ return totalVP(player); }
function eligibleBootRecipients(holder){
  const score=publicVP(holder);
  return game.players.filter(p=>p.id!==holder.id&&publicVP(p)>=score);
}
function transferOldBoot(fromId,toId){
  if(game.oldBootHolder!==fromId) return false;
  const from=playerById(fromId),to=playerById(toId);
  if(!to || publicVP(to)<publicVP(from)) return false;
  game.oldBootHolder=toId;
  queueAwardEvent("oldBoot",toId);
  log(`${from.name}がボロ靴を${to.name}へ渡しました。`);
  checkVictory(); render(); return true;
}
function transferOldBootHuman(){
  const p=currentPlayer();
  if(!game.fishermen || game.phase!=="turn" || !isLocalPlayer(p) || game.oldBootHolder!==p.id) return;
  const candidates=eligibleBootRecipients(p);
  if(!candidates.length){
    log("勝利点が同点以上の相手がいないため、ボロ靴を渡せません。");
    return;
  }
  openChoiceModal({
    title:"ボロ靴を渡す",
    guide:"自分と同点以上の勝利点を持つ相手を選択してください。",
    options:playerChoiceOptions(candidates,player=>`勝利点 ${publicVP(player)}点`),
    onSelect:targetId=>{
      cpuAnalysisQueueHumanReceipt(
        p,
        "transfer_old_boot",
        {targetId}
      );
      transferOldBoot(p.id,targetId);
    },
    allowCancel:true,
  });
}
function cpuTransferBoot(player){
  if(game.oldBootHolder!==player.id) return false;
  const candidates=eligibleBootRecipients(player).sort((a,b)=>publicVP(b)-publicVP(a));
  if(!candidates.length) return false;
  const target=candidates[0];
  const moved=transferOldBoot(player.id,target.id);
  if(moved){
    cpuAnalysisRecordAction(player,"transfer_old_boot",{
      targetId:target.id,
      targetName:target.name,
      candidateIds:candidates.map(candidate=>candidate.id),
    });
  }
  return moved;
}
function cpuSpendFish(player,cost,reason){
  const payment=findFishPayment(player.fishTokens,cost);
  if(!payment) return false;
  spendFish(player,payment.indices,cost,reason); return true;
}
function robberHurtsPlayer(player){
  if(game.robberHex===null) return false;
  return game.board.hexes[game.robberHex].corners.some(vid=>game.board.vertices[vid].building?.player===player.id);
}
function cpuUseFish(player,maxActions=3){
  if(!game.fishermen) return 0;

  let actions=0;
  const actionLimit=Math.max(1,Number(maxActions)||1);

  while(actions<actionLimit){
    const tokensBefore=[...player.fishTokens];

    if(
      robberHurtsPlayer(player) &&
      game.robberHex!==null &&
      findFishPayment(
        player.fishTokens,
        2
      )
    ){
      const oldRobberHex=game.robberHex;
      cpuSpendFish(
        player,
        2,
        "🐱を盤外へ"
      );

      game.robberHex=null;

      queueAwardEvent(
        "fishRemoveRobber",
        player.id
      );

      cpuAnalysisRecordAction(
        player,
        "fish_remove_robber",
        {cost:2,robberHex:oldRobberHex,tokensBefore}
      );

      log(
        `${player.name}が魚で`+
        "🐱を盤外へ追い出しました。"
      );

      actions++;
      continue;
    }

    const goal=
      cpuChooseGoal(player);

    const missing=
      cpuGoalMissingResources(
        player,
        goal
      );

    if(
      missing.length &&
      findFishPayment(
        player.fishTokens,
        4
      )
    ){
      const resource=
        missing.find(
          item=>
            game.bank[
              item.resource
            ]>0
        )?.resource;

      if(resource){
        cpuSpendFish(
          player,
          4,
          `${RESOURCE_JA[resource]}獲得`
        );

        const got=
          gainResource(
            player,
            resource,
            1
          );

        showResourceDelta(
          player.id,
          {[resource]:got},
          "魚4匹"
        );

        cpuAnalysisRecordAction(
          player,
          "fish_resource",
          {
            cost:4,
            resource,
            got,
            tokensBefore,
            goal:goal?cpuAnalysisGoalSummary(player,goal):null,
          }
        );

        actions++;
        continue;
      }
    }

    if(
      player.pieces.road>0 &&
      findFishPayment(
        player.fishTokens,
        5
      )
    ){
      const bestRoad=
        cpuBestRoadTarget(player);

      if(
        bestRoad &&
        bestRoad.score>=13
      ){
        cpuSpendFish(
          player,
          5,
          "無料街道"
        );

        placeRoad(
          player.id,
          bestRoad.id,
          true
        );

        cpuAnalysisRecordAction(
          player,
          "fish_free_road",
          {
            cost:5,
            edgeId:bestRoad.id,
            roadScore:cpuAnalysisRound(bestRoad.score),
            awardGain:bestRoad.awardGain||0,
            tokensBefore,
          }
        );

        log(
          `${player.name}が魚で`+
          "無料街道を建てました。"
        );

        actions++;
        continue;
      }
    }

    if(
      findFishPayment(
        player.fishTokens,
        3
      )
    ){
      const candidates=
        game.players.filter(
          other=>
            other.id!==player.id &&
            totalResources(other)>0
        );

      const victim=
        cpuChooseVictimFromCandidates(
          candidates,
          player.id
        );

      if(
        victim &&
        (
          totalResources(victim)>=5 ||
          publicVP(victim)>=7
        )
      ){
        const victimScore=cpuVictimScore(victim,player);
        cpuSpendFish(
          player,
          3,
          "資源強奪"
        );

        stealRandom(
          player.id,
          victim.id,
          "魚3匹"
        );

        cpuAnalysisRecordAction(
          player,
          "fish_steal",
          {
            cost:3,
            victimId:victim.id,
            victimName:victim.name,
            victimScore:cpuAnalysisRound(victimScore),
            tokensBefore,
          }
        );

        actions++;
        continue;
      }
    }

    if(
      game.devDeck.length &&
      findFishPayment(
        player.fishTokens,
        7
      )
    ){
      cpuSpendFish(
        player,
        7,
        "無料発展カード"
      );

      if(
        grantFreeDevelopmentCard(
          player,
          `${player.name}の魚7匹`
        )
      ){
        cpuAnalysisRecordAction(
          player,
          "fish_free_development",
          {cost:7,tokensBefore}
        );
        actions++;
        continue;
      }
    }

    cpuAnalysisRecordEvent(
      "fish_decision",
      player,
      {
        selected:null,
        reason:"no_fish_action_worth_using",
        tokens:[...player.fishTokens],
        totalFish:player.fishTokens.reduce((sum,token)=>sum+(typeof token==="number"?token:0),0),
        robberHurtsSelf:robberHurtsPlayer(player),
        goal:goal?cpuAnalysisGoalSummary(player,goal):null,
        missing:cpuAnalysisClone(missing),
      },
      `fish-none:${game.turnSerial}:${player.id}:${player.fishTokens.join(".")}`
    );

    break;
  }

  return actions;
}


function removeDevCard(player,card){
  const index=player.dev.findIndex(item=>item===card);
  if(index<0) return false;
  player.dev.splice(index,1);
  return true;
}

function chooseYearOfPlentyResources(player,selected=[]){
  if(selected.length>=2){
    cpuAnalysisQueueHumanReceipt(
      player,
      "play_development",
      {card:"yearOfPlenty",resources:[...selected]}
    );
    if(!removeDevCard(player,"yearOfPlenty")) return;
    queueAwardEvent("devDiscovery",player.id);
    const delta={};
    for(const resource of selected){
      const got=gainResource(player,resource,1);
      if(got) delta[resource]=(delta[resource]||0)+got;
    }
    showResourceDelta(player.id,delta,"発見");
    log("発見を使い、資源を2枚まで獲得しました。");
    checkVictory();
    render();
    return;
  }
  openResourceChoice(
    "発見",
    `獲得する資源を選択してください（${selected.length+1}/2枚目）。`,
    resource=>chooseYearOfPlentyResources(player,[...selected,resource]),
    {filter:resource=>game.bank[resource]>0}
  );
}

function playDev(card){
  const p=currentPlayer();
  if(!isLocalPlayer(p) || game.phase!=="turn") return;
  if(!p.dev.includes(card)) return;

  if(card==="yearOfPlenty"){
    if(!RESOURCES.some(resource=>game.bank[resource]>0)){
      log("銀行に獲得できる資源がありません。");
      return;
    }
    chooseYearOfPlentyResources(p,[]);
    return;
  }

  if(card==="monopoly"){
    openResourceChoice(
      "独占",
      "全プレイヤーから集める資源を選択してください。",
      resource=>{
        cpuAnalysisQueueHumanReceipt(
          p,
          "play_development",
          {card:"monopoly",resource}
        );
        if(!removeDevCard(p,"monopoly")) return;
        queueAwardEvent("devMonopoly",p.id);
        let amount=0;
        game.players.forEach(other=>{
          if(other.id===p.id) return;
          const taken=other.resources[resource];
          if(taken){
            amount+=taken;
            p.resources[resource]+=taken;
            other.resources[resource]=0;
            showResourceDelta(other.id,{[resource]:-taken},"独占");
          }
        });
        showResourceDelta(p.id,{[resource]:amount},"独占");
        log(`独占を使い、${RESOURCE_JA[resource]}を${amount}枚集めました。`);
        checkVictory();
        render();
      },
      {
        amountLabel:resource=>`他プレイヤー合計：${game.players.filter(x=>x.id!==p.id).reduce((s,x)=>s+x.resources[resource],0)}枚`,
        filter:()=>true
      }
    );
    return;
  }

  cpuAnalysisQueueHumanReceipt(
    p,
    "play_development",
    {card}
  );
  if(!removeDevCard(p,card)) return;
  if(card==="vp"){
    queueAwardEvent("devVictoryPoint",p.id);
    p.revealedVP++;
    log(`${p.name}が勝利ポイントカードを公開しました。`);
  } else if(card==="knight"){
    queueAwardEvent("devKnight",p.id);
    p.knightsPlayed++;
    updateAwards();
    game.phase="moveRobber";
    game.robberMover=p.id;
    game.robberAfterKnight=true;
    log("騎士を使いました。🐱を移動してください。");
  } else if(card==="roadBuilding"){
    queueAwardEvent("devRoadBuilding",p.id);
    game.freeRoads=Math.min(2,p.pieces.road);
    game.buildMode="road";
    log(`街道建設を使いました。無料で街道を${game.freeRoads}本置けます。`);
  }
  checkVictory();
  render();
}

function endTurn(){
  const p=currentPlayer();
  if(!isLocalPlayer(p) || game.phase!=="turn" || !game.rolled || game.freeRoads>0 || game.winner || game.diceRolling) return;
  cpuAnalysisQueueHumanReceipt(p,"end_turn",{});
  finishActivePhase();
}

function resetActivePlayerState(p){
  p.builtThisTurn=false;
  game.buildMode=null;
  game.freeRoads=0;
  game.phase="turn";
  if(p.human) game.selectedFishIndices=[];
}

function finishActivePhase(){
  cpuActionRunning=false;
  clearTimeout(cpuTimer);
  cpuTimer=null;
  cpuScheduledKey=null;
  const old=currentPlayer();
  if(old && !old.human){
    cpuAnalysisRecordAction(old,"turn_end",{
      turnSerial:game.turnSerial,
      turnNo:game.turnNo,
    });
  }
  resetActivePlayerState(old);
  const nextPlayer=(game.current+1)%game.playerCount;
  if(nextPlayer===0) game.turnNo++;
  game.current=nextPlayer;
  game.turnSerial++;
  game.rolled=false;
  game.dice=[0,0];
  game.turnDice=[0,0];
  game.phase="turn";
  queueTurnAnnouncement(game.current);
  render();
  scheduleCpuIfNeeded();
}

function nextTurn(){
  finishActivePhase();
}

function scheduleCpu(){
  if(ONLINE_MODE && !isOnlineHost()) return;

  clearTimeout(cpuTimer);
  cpuTimer=null;

  if(
    !game ||
    game.winner ||
    !currentPlayer() ||
    currentPlayer().human ||
    game.diceRolling ||
    cpuActionRunning
  ){
    cpuScheduledKey=null;
    return;
  }

  const scheduledKey=[
    game.current,
    game.phase,
    game.setupIndex,
    game.turnSerial,
    game.rolled?1:0,
  ].join(":");
  cpuScheduledKey=scheduledKey;

  cpuTimer=setTimeout(()=>{
    cpuTimer=null;

    if(
      !game ||
      game.winner ||
      !currentPlayer() ||
      currentPlayer().human ||
      game.diceRolling ||
      cpuActionRunning
    ){
      cpuScheduledKey=null;
      return;
    }

    const currentKey=[
      game.current,
      game.phase,
      game.setupIndex,
      game.turnSerial,
      game.rolled?1:0,
    ].join(":");

    if(currentKey!==scheduledKey || cpuScheduledKey!==scheduledKey){
      return;
    }

    cpuScheduledKey=null;
    cpuAct();
  },CPU_ACTION_DELAY_MS);
}

function cpuAct(){
  if(!game || game.winner){
    cpuActionRunning=false;
    return;
  }

  const p=currentPlayer();
  if(!p || p.human){
    cpuActionRunning=false;
    clearTimeout(cpuTimer);
    cpuTimer=null;
    cpuScheduledKey=null;
    return;
  }

  if(game.phase==="setupSettlement"){
    const v=bestSetupVertex(p.id);
    placeSettlement(p.id,v,true); game.setupVertex=v; game.phase="setupRoad";
    cpuAnalysisRecordAction(p,"setup_settlement",{vertexId:v});
    log(`${p.name}が初期開拓地を置きました。`);
    render();
    scheduleCpuIfNeeded();
    return;
  }
  if(game.phase==="setupRoad"){
    const options=game.board.vertices[game.setupVertex].edges.filter(e=>canPlaceRoad(p.id,e,game.setupVertex));
    const scored=options.map(edgeId=>({
      id:edgeId,
      score:futureVertexScore(
        otherEnd(
          edgeId,
          game.setupVertex
        ),
        p.id
      ),
    })).sort((a,b)=>b.score-a.score);

    cpuAnalysisRecordSetupRoad(
      p,
      scored
    );

    const e=
      scored[0]?.id||
      options[options.length-1];
    game.board.edges[e].road=p.id; p.roads.push(e); p.pieces.road--;
    cpuAnalysisRecordAction(p,"setup_road",{edgeId:e});
    log(`${p.name}が初期街道を置きました。`);
    advanceSetup(); return;
  }
  if(game.phase==="moveRobber"){
    const playerId=p.id;
    cpuMoveRobber(playerId);
    clearTimeout(cpuTimer);
    cpuTimer=setTimeout(
      ()=>cpuBuildPhase(playerId,"fish"),
      CPU_ACTION_DELAY_MS
    );
    return;
  }
  if(game.phase!=="turn"){
    cpuActionRunning=false;
    return;
  }

  const playerId=p.id;

  /*
    v1.54:
    CPUがすでにダイスを振った後で、魚交換・再接続・手動復旧などにより
    CPU処理だけ再スケジュールされた場合は、絶対にダイスを振り直さない。
    そのターンのダイス後処理（魚→発展→交易→建設）から再開する。
  */
  if(game.rolled){
    cpuActionRunning=true;
    cpuBuildPhase(playerId,"fish");
    return;
  }

  cpuActionRunning=true;
  cpuAnalysisRecordTurnStart(p);

  if(game.fishermen){
    const movedBoot=cpuTransferBoot(p);
    if(game.winner){
      cpuActionRunning=false;
      return;
    }

    if(movedBoot){
      render();
      clearTimeout(cpuTimer);
      cpuTimer=setTimeout(()=>{
        cpuTimer=null;
        const current=playerById(playerId);
        if(
          !game ||
          game.winner ||
          !current ||
          current.human ||
          game.current!==playerId
        ){
          cpuActionRunning=false;
          return;
        }
        animateDiceRoll(
          playerId,
          ()=>cpuBuildPhase(playerId,"fish")
        );
      },CPU_ACTION_DELAY_MS);
      return;
    }
  }

  animateDiceRoll(
    playerId,
    ()=>cpuBuildPhase(playerId,"fish")
  );
}

function scheduleCpuBuildStep(playerId,stage,delay=CPU_ACTION_DELAY_MS){
  clearTimeout(cpuTimer);
  cpuTimer=setTimeout(()=>{
    cpuTimer=null;

    const player=playerById(playerId);
    if(
      !game ||
      game.winner ||
      !player ||
      player.human ||
      game.current!==playerId
    ){
      cpuActionRunning=false;
      return;
    }

    cpuBuildPhase(playerId,stage);
  },delay);
}

function cpuBuildPhase(playerOrId,stage="fish"){
  const playerId=
    typeof playerOrId==="object"
      ?playerOrId?.id
      :playerOrId;

  const p=playerById(playerId);

  if(
    !game ||
    game.winner ||
    !p ||
    p.human ||
    game.current!==playerId
  ){
    cpuActionRunning=false;
    return;
  }

  cpuActionRunning=true;

  /*
    v1.50:
    1回の呼び出しで「盤面を変える行動」は最大1種類だけ実行する。
    実際に何かした時だけ2秒待って次段階へ進む。
    評価・候補探索などの内部計算には待機を入れない。
  */
  let currentStage=stage;

  while(true){
    if(currentStage==="fish"){
      const fishActions=cpuUseFish(p,1);
      checkVictory();

      if(game.winner){
        cpuActionRunning=false;
        render();
        return;
      }

      if(fishActions>0){
        updateAwards();
        render();
        scheduleCpuBuildStep(playerId,"fish");
        return;
      }

      currentStage="dev";
      continue;
    }

    if(currentStage==="dev"){
      cpuAnalysisRecordGoalDecision(p,"dev");
      const devResult=cpuUseStrategicDevelopment(p);

      if(devResult==="finished"){
        cpuActionRunning=false;
        render();
        return;
      }

      // 騎士は盗賊移動を含むため、cpuPlayKnight側で続きを予約する。
      if(devResult==="knight"){
        return;
      }

      if(devResult==="action"){
        updateAwards();
        checkVictory();
        render();

        if(game.winner){
          cpuActionRunning=false;
          return;
        }

        scheduleCpuBuildStep(playerId,"dev");
        return;
      }

      currentStage="trade";
      continue;
    }

    if(currentStage==="trade"){
      cpuAnalysisRecordGoalDecision(p,"player_trade");
      if(
        !p.builtThisTurn &&
        cpuTryPlayerTrade(p)
      ){
        render();
        scheduleCpuBuildStep(playerId,"bank");
        return;
      }

      currentStage="bank";
      continue;
    }

    if(currentStage==="bank"){
      const goal=cpuChooseGoal(p);
      cpuAnalysisRecordGoalDecision(p,"bank_trade",goal);

      if(
        !p.builtThisTurn &&
        goal &&
        !cpuGoalBuildable(p,goal) &&
        cpuTryBankTrade(p)
      ){
        render();
        scheduleCpuBuildStep(playerId,"bank");
        return;
      }

      currentStage="build";
      continue;
    }

    if(currentStage==="build"){
      let goal=cpuChooseGoal(p);
      cpuAnalysisRecordGoalDecision(p,"build",goal);
      let built=false;

      if(
        !p.builtThisTurn &&
        goal &&
        cpuGoalBuildable(p,goal)
      ){
        built=cpuExecuteGoal(p,goal);
      }

      /*
        目標資源を崩してまで毎ターン無理に建てない。
        ただし8枚以上で7の破棄リスクが高い場合だけ、
        戦略点が近い建設候補へ資源圧縮として逃がす。
      */
      if(
        !built &&
        !p.builtThisTurn &&
        totalResources(p)>=8
      ){
        const goals=cpuStrategicGoals(p);
        const primaryScore=goal?.strategicScore??-Infinity;

        const emergency=goals.find(candidate=>
          cpuGoalBuildable(p,candidate) &&
          candidate.strategicScore>=primaryScore-18
        );

        if(emergency){
          built=cpuExecuteGoal(p,emergency);
        }
      }

      updateAwards();
      checkVictory();
      render();

      if(game.winner){
        cpuActionRunning=false;
        return;
      }

      // 建設をした場合も、何も建てなかった場合もターン終了前に2秒置く。
      scheduleCpuBuildStep(playerId,"finish");
      return;
    }

    if(currentStage==="finish"){
      const current=playerById(playerId);
      if(
        !game ||
        game.winner ||
        !current ||
        current.human ||
        game.current!==playerId
      ){
        cpuActionRunning=false;
        return;
      }

      finishActivePhase();
      return;
    }

    // 不明な段階は安全側でターン終了へ。
    currentStage="finish";
  }
}

function cpuHasBuildOption(p){
  if(p.pieces.city>0 && hasCost(p,COST.city) && p.settlements.length) return true;
  if(p.pieces.settlement>0 && hasCost(p,COST.settlement) &&
     Object.keys(game.board.vertices).some(v=>canPlaceSettlement(p.id,v,false))) return true;
  if(p.pieces.road>0 && hasCost(p,COST.road) &&
     Object.keys(game.board.edges).some(e=>canPlaceRoad(p.id,e))) return true;
  if(game.devDeck.length && hasCost(p,COST.dev)) return true;
  return false;
}

function cpuTryBankTrade(p){
  const goal=
    cpuChooseGoal(p);

  if(!goal?.cost){
    cpuAnalysisRecordEvent(
      "bank_trade_decision",
      p,
      {
        selected:null,
        candidates:[],
        reason:"no_goal",
      }
    );
    return false;
  }

  const beforeDistance=
    cpuGoalDistance(
      p,
      goal
    );

  const candidates=[];

  for(const receiveResource of RESOURCES){
    if(
      game.bank[receiveResource]<1
    ){
      continue;
    }

    for(const giveResource of RESOURCES){
      if(
        giveResource===
        receiveResource
      ){
        continue;
      }

      const rate=
        getTradeRate(
          p,
          giveResource
        );

      if(
        p.resources[giveResource]<
        rate
      ){
        continue;
      }

      const simulated=
        cpuSimulatedResources(
          p,
          {
            [giveResource]:-rate,
            [receiveResource]:1,
          }
        );

      const afterDistance=
        cpuGoalDistance(
          p,
          goal,
          simulated
        );

      const improvement=
        beforeDistance-
        afterDistance;

      const sevenRiskBonus=
        totalResources(p)>=8
          ?0.45
          :0;

      const score=
        improvement+
        sevenRiskBonus-
        rate*.04;

      if(score<=.08){
        continue;
      }

      candidates.push({
        giveResource,
        receiveResource,
        rate,
        beforeDistance,
        afterDistance,
        improvement,
        sevenRiskBonus,
        score,
      });
    }
  }

  candidates.sort(
    (a,b)=>b.score-a.score
  );

  const best=candidates[0]||null;

  cpuAnalysisRecordEvent(
    "bank_trade_decision",
    p,
    {
      goal:cpuAnalysisGoalSummary(p,goal),
      selected:best?cpuAnalysisClone(best):null,
      candidates:candidates.slice(0,20).map((candidate,index)=>({
        rank:index+1,
        ...cpuAnalysisClone(candidate),
        score:cpuAnalysisRound(candidate.score),
        improvement:cpuAnalysisRound(candidate.improvement),
        beforeDistance:cpuAnalysisRound(candidate.beforeDistance),
        afterDistance:cpuAnalysisRound(candidate.afterDistance),
      })),
      stateBefore:cpuAnalysisStateSnapshot(p),
    }
  );

  if(!best){
    return false;
  }

  p.resources[
    best.giveResource
  ]-=best.rate;

  game.bank[
    best.giveResource
  ]+=best.rate;

  p.resources[
    best.receiveResource
  ]++;

  game.bank[
    best.receiveResource
  ]--;

  showResourceDelta(
    p.id,
    {
      [best.giveResource]:
        -best.rate,
      [best.receiveResource]:
        1,
    },
    "銀行・港交易"
  );

  cpuAnalysisRecordAction(
    p,
    "bank_trade",
    {
      giveResource:best.giveResource,
      receiveResource:best.receiveResource,
      rate:best.rate,
      score:cpuAnalysisRound(best.score),
      improvement:cpuAnalysisRound(best.improvement),
      goalKey:cpuGoalKey(goal),
    }
  );

  log(
    `${p.name}が`+
    `${RESOURCE_JA[best.giveResource]}`+
    `${best.rate}枚を`+
    `${RESOURCE_JA[best.receiveResource]}`+
    "1枚へ交易しました。"
  );

  return true;
}


function cpuPlayVictoryPoint(p){
  const idx=p.dev.findIndex(c=>c==="vp");
  if(idx<0 || usableDevCount(p,"vp")<=0) return;
  p.dev.splice(idx,1);
  queueAwardEvent("devVictoryPoint",p.id);
  p.revealedVP++;
  cpuAnalysisRecordAction(p,"dev_victory_point",{revealedVP:p.revealedVP});
  log(`${p.name}が勝利ポイントカードを公開しました。`);
  checkVictory();
}

function cpuPlayYearOfPlenty(p){
  if(
    usableDevCount(
      p,
      "yearOfPlenty"
    )<=0
  ){
    return false;
  }

  const goal=cpuChooseGoal(p);
  const selected=[];
  const simulated={
    ...p.resources,
  };

  for(let draw=0;draw<2;draw++){
    const planCost=
      goal?.cost
        ?cpuGoalPlanCost(goal)
        :null;

    const missing=
      planCost
        ?RESOURCES
          .filter(resource=>
            game.bank[resource]>0 &&
            simulated[resource]<
              (planCost[resource]||0)
          )
          .sort(
            (a,b)=>
              (
                (planCost[b]||0)-
                simulated[b]
              )-
              (
                (planCost[a]||0)-
                simulated[a]
              )
          )
        :[];

    let resource=missing[0];

    if(!resource){
      resource=
        RESOURCES
          .filter(
            candidate=>
              game.bank[candidate]>0
          )
          .sort(
            (a,b)=>
              cpuResourceKeepValue(
                p,
                b,
                goal
              )-
              cpuResourceKeepValue(
                p,
                a,
                goal
              )
          )[0];
    }

    if(!resource) break;

    selected.push(resource);
    simulated[resource]++;
  }

  if(!selected.length) return false;

  const index=
    p.dev.indexOf(
      "yearOfPlenty"
    );

  if(index<0) return false;

  p.dev.splice(index,1);
  queueAwardEvent(
    "devDiscovery",
    p.id
  );

  const delta={};

  for(const resource of selected){
    const got=
      gainResource(
        p,
        resource,
        1
      );

    if(got){
      delta[resource]=
        (delta[resource]||0)+got;
    }
  }

  showResourceDelta(
    p.id,
    delta,
    "発見"
  );

  cpuAnalysisRecordAction(
    p,
    "dev_year_of_plenty",
    {selectedResources:[...selected],delta,goalKey:goal?cpuGoalKey(goal):null}
  );

  log(
    `${p.name}が発見を使い、`+
    `${selected.map(
      resource=>RESOURCE_JA[resource]
    ).join("・")}を獲得しました。`
  );

  return true;
}

function cpuPlayMonopoly(p){
  if(
    usableDevCount(
      p,
      "monopoly"
    )<=0
  ){
    return false;
  }

  const best=
    cpuBestMonopolyResource(p);

  if(
    !best ||
    best.othersTotal<=0
  ){
    return false;
  }

  const threshold=
    publicVP(p)>=7
      ?2
      :3;

  if(
    best.othersTotal<threshold &&
    !best.immediateWin &&
    !(
      publicVP(p)>=8 &&
      best.improvement>=1.4
    )
  ){
    return false;
  }

  const index=
    p.dev.indexOf(
      "monopoly"
    );

  if(index<0) return false;

  p.dev.splice(index,1);

  queueAwardEvent(
    "devMonopoly",
    p.id
  );

  let amount=0;

  for(const other of game.players){
    if(other.id===p.id) continue;

    const taken=
      other.resources[
        best.resource
      ]||0;

    if(!taken) continue;

    amount+=taken;
    p.resources[best.resource]+=taken;
    other.resources[best.resource]=0;

    showResourceDelta(
      other.id,
      {[best.resource]:-taken},
      "独占"
    );
  }

  showResourceDelta(
    p.id,
    {[best.resource]:amount},
    "独占"
  );

  cpuAnalysisRecordAction(
    p,
    "dev_monopoly",
    {
      resource:best.resource,
      amount,
      score:cpuAnalysisRound(best.score),
      improvement:cpuAnalysisRound(best.improvement),
      immediateWin:!!best.immediateWin,
      othersTotal:best.othersTotal,
    }
  );

  log(
    `${p.name}が独占を使い、`+
    `${RESOURCE_JA[best.resource]}を`+
    `${amount}枚集めました。`
  );

  return true;
}

function cpuPlayRoadBuilding(p){
  if(
    usableDevCount(
      p,
      "roadBuilding"
    )<=0 ||
    p.pieces.road<=0
  ){
    return false;
  }

  const first=
    cpuBestRoadTarget(p);

  if(!first) return false;

  const index=
    p.dev.indexOf(
      "roadBuilding"
    );

  if(index<0) return false;

  p.dev.splice(index,1);

  queueAwardEvent(
    "devRoadBuilding",
    p.id
  );

  let placed=0;
  const placedEdges=[];

  for(let count=0;count<2;count++){
    if(p.pieces.road<=0) break;

    const best=
      cpuBestRoadTarget(p);

    if(!best) break;

    placeRoad(
      p.id,
      best.id,
      true
    );

    placedEdges.push(best.id);
    placed++;
  }

  if(!placed){
    return false;
  }

  cpuAnalysisRecordAction(
    p,
    "dev_road_building",
    {placedEdges,placed}
  );

  log(
    `${p.name}が街道建設を使い、`+
    `無料で街道を${placed}本建てました。`
  );

  return true;
}

function cpuUseStrategicDevelopment(p){
  /*
    v1.50: 1回の呼び出しにつき発展カード系の見える行動は1つだけ。
    次のカード判断は2秒後に再評価する。
  */
  const usable={
    vp:usableDevCount(p,"vp"),
    yearOfPlenty:usableDevCount(p,"yearOfPlenty"),
    monopoly:usableDevCount(p,"monopoly"),
    roadBuilding:usableDevCount(p,"roadBuilding"),
    knight:usableDevCount(p,"knight"),
  };
  const vpCount=usable.vp;
  const neededForWin=Math.max(0,victoryTarget(p)-totalVP(p));

  if(vpCount>0 && neededForWin>0 && neededForWin<=vpCount){
    cpuAnalysisRecordEvent(
      "development_decision",
      p,
      {selected:"victory_point",usable,neededForWin,reason:"enough_hidden_vp_to_win"}
    );
    cpuPlayVictoryPoint(p);
    return game.winner ?"finished":"action";
  }

  const canYearOfPlenty=cpuCanYearOfPlentyHelp(p);
  if(canYearOfPlenty){
    cpuAnalysisRecordEvent(
      "development_decision",
      p,
      {
        selected:"year_of_plenty",
        usable,
        neededForWin,
        reason:"goal_missing_one_or_two_resources",
        goal:cpuAnalysisGoalSummary(p,cpuChooseGoal(p)),
      }
    );
    if(cpuPlayYearOfPlenty(p)){
      return "action";
    }
  }

  const monopolyCandidate=usable.monopoly>0
    ?cpuBestMonopolyResource(p)
    :null;
  if(cpuPlayMonopoly(p)){
    cpuAnalysisRecordEvent(
      "development_decision",
      p,
      {
        selected:"monopoly",
        usable,
        neededForWin,
        candidate:cpuAnalysisClone(monopolyCandidate),
      }
    );
    return "action";
  }

  const goal=cpuChooseGoal(p);
  const roadBuildingPlan=
    usable.roadBuilding>0
      ?cpuBestRoadSequence(p,Math.min(2,p.pieces.road))
      :null;

  if(
    usable.roadBuilding>0 &&
    (
      goal?.kind==="road" ||
      roadBuildingPlan?.awardGain>0 ||
      roadBuildingPlan?.immediateWin ||
      (
        !cpuBestSettlementTarget(p) &&
        roadBuildingPlan?.sequence?.length
      )
    ) &&
    cpuPlayRoadBuilding(p)
  ){
    cpuAnalysisRecordEvent(
      "development_decision",
      p,
      {
        selected:"road_building",
        usable,
        neededForWin,
        goal:goal?cpuAnalysisGoalSummary(p,goal):null,
        roadBuildingPlan:cpuAnalysisClone(roadBuildingPlan),
      }
    );
    return "action";
  }

  const shouldKnight=cpuShouldPlayKnight(p);
  if(shouldKnight){
    cpuAnalysisRecordEvent(
      "development_decision",
      p,
      {
        selected:"knight",
        usable,
        neededForWin,
        goal:goal?cpuAnalysisGoalSummary(p,goal):null,
        robberHurtsSelf:robberHurtsPlayer(p),
        bestRobberHexId:cpuBestRobberHexId(p.id),
      }
    );
    cpuPlayKnight(p);
    return "knight";
  }

  cpuAnalysisRecordEvent(
    "development_decision",
    p,
    {
      selected:null,
      usable,
      neededForWin,
      canYearOfPlenty,
      monopolyCandidate:cpuAnalysisClone(monopolyCandidate),
      roadBuildingPlan:cpuAnalysisClone(roadBuildingPlan),
      shouldKnight,
      goal:goal?cpuAnalysisGoalSummary(p,goal):null,
      reason:"no_development_card_meets_use_threshold",
    },
    `dev-none:${game.turnSerial}:${p.id}:${p.dev.join(".")}:${RESOURCES.map(r=>p.resources[r]).join(".")}`
  );

  return "done";
}


function cpuPlayKnight(p){
  const idx=p.dev.indexOf("knight");
  if(idx<0) return;

  p.dev.splice(idx,1);
  queueAwardEvent("devKnight",p.id);
  p.knightsPlayed++;
  updateAwards();
  cpuAnalysisRecordAction(
    p,
    "dev_knight",
    {knightsPlayed:p.knightsPlayed,robberHurtsSelf:robberHurtsPlayer(p)}
  );
  log(`${p.name}が騎士を使いました。`);

  game.phase="moveRobber";
  game.robberMover=p.id;

  const playerId=p.id;
  render();

  // 騎士使用 → 2秒 → 盗賊移動 → 2秒 → 残りのCPU行動。
  clearTimeout(cpuTimer);
  cpuTimer=setTimeout(()=>{
    cpuTimer=null;

    const current=playerById(playerId);
    if(
      !game ||
      game.winner ||
      game.current!==playerId ||
      !current ||
      current.human ||
      game.phase!=="moveRobber"
    ){
      cpuActionRunning=false;
      return;
    }

    cpuMoveRobber(playerId);

    clearTimeout(cpuTimer);
    cpuTimer=setTimeout(()=>{
      cpuTimer=null;
      const latest=playerById(playerId);
      if(
        !game ||
        game.winner ||
        game.current!==playerId ||
        !latest ||
        latest.human
      ){
        cpuActionRunning=false;
        return;
      }
      cpuBuildPhase(playerId,"dev");
    },CPU_ACTION_DELAY_MS);
  },CPU_ACTION_DELAY_MS);
}

function usableDevCount(p,card){
  return p.dev.filter(c=>c===card).length;
}
function otherEnd(edgeId,vertexId){
  const e=game.board.edges[edgeId];
  return e.a===vertexId
    ?e.b
    :e.a;
}

function futureVertexScore(
  vertexId,
  playerId=currentPlayer()?.id
){
  if(
    playerId===undefined ||
    playerId===null
  ){
    return vertexProductionScore(
      vertexId
    );
  }

  return cpuVertexStrategicScore(
    vertexId,
    playerId,
    {setup:true}
  );
}

function cpuSetupPairPotential(
  playerId,
  firstVertexId
){
  const player=playerById(playerId);

  if(
    !player ||
    player.settlements.length>0
  ){
    return 0;
  }

  const firstVertex=
    game.board.vertices[firstVertexId];

  if(!firstVertex) return 0;

  const firstResources=new Set();
  const firstNumbers=new Set();

  for(const hexId of firstVertex.hexes){
    const hex=game.board.hexes[hexId];
    if(!hex) continue;
    if(RESOURCES.includes(hex.resource)){
      firstResources.add(hex.resource);
    }
    if(hex.number){
      firstNumbers.add(hex.number);
    }
  }

  let bestSecond=-9999;

  for(const secondId of Object.keys(game.board.vertices)){
    if(secondId===firstVertexId) continue;

    if(
      vertexNeighbors(firstVertexId)
        .includes(secondId)
    ){
      continue;
    }

    if(
      !canPlaceSettlement(
        playerId,
        secondId,
        true
      )
    ){
      continue;
    }

    const secondVertex=
      game.board.vertices[secondId];

    let score=
      cpuVertexStrategicScore(
        secondId,
        playerId,
        {setup:true}
      );

    const combinedResources=
      new Set(firstResources);

    let overlapNumbers=0;

    for(const hexId of secondVertex.hexes){
      const hex=game.board.hexes[hexId];
      if(!hex) continue;

      if(RESOURCES.includes(hex.resource)){
        combinedResources.add(hex.resource);
      }

      if(
        hex.number &&
        firstNumbers.has(hex.number)
      ){
        overlapNumbers++;
      }
    }

    score+=
      combinedResources.size*1.8;

    if(
      combinedResources.has("grain") &&
      combinedResources.has("ore")
    ){
      score+=4.5;
    }

    if(
      combinedResources.has("wood") &&
      combinedResources.has("brick")
    ){
      score+=3.7;
    }

    if(combinedResources.size===5){
      score+=6.5;
    }

    score-=overlapNumbers*1.7;

    bestSecond=
      Math.max(
        bestSecond,
        score
      );
  }

  if(bestSecond<=-9000){
    return 0;
  }

  /*
    1軒目単体の価値を主役にしつつ、
    2軒セットとして強い初期配置を選びやすくする。
  */
  return bestSecond*.34;
}

function bestSetupVertex(playerId){
  const player=playerById(playerId);

  const candidates=
    Object.keys(game.board.vertices)
      .filter(vertexId=>
        canPlaceSettlement(
          playerId,
          vertexId,
          true
        )
      );

  const scored=candidates.map(vertexId=>{
    const baseScore=
      setupVertexScore(
        vertexId,
        playerId
      );

    const pairPotential=
      player?.settlements.length===0
        ?cpuSetupPairPotential(
          playerId,
          vertexId
        )
        :0;

    return {
      id:vertexId,
      baseScore,
      pairPotential,
      score:baseScore+pairPotential,
    };
  });

  scored.sort((a,b)=>b.score-a.score);

  cpuAnalysisRecordSetupSettlement(
    playerId,
    scored
  );

  return scored[0]?.id??null;
}

function setupVertexScore(
  vertexId,
  playerId
){
  return cpuVertexStrategicScore(
    vertexId,
    playerId,
    {setup:true}
  );
}

function vertexProductionScore(v){
  return game.board.vertices[v].hexes.reduce((s,h)=>{
    const x=game.board.hexes[h];

    if(x.number){
      return s+(PIPS[x.number]||0);
    }

    if(x.resource==="lake"){
      return (
        s+
        x.lakeNumbers.reduce(
          (n,value)=>
            n+(PIPS[value]||0),
          0
        )*.45
      );
    }

    return s;
  },0);
}

function cpuRoadEndpointPotential(
  vertexId,
  playerId
){
  const vertex=
    game.board.vertices[vertexId];

  if(!vertex) return -9999;

  let score=0;

  if(!vertex.building){
    const blockedByNeighbor=
      vertexNeighbors(vertexId)
        .some(neighborId=>
          !!game.board.vertices[
            neighborId
          ].building
        );

    if(!blockedByNeighbor){
      score +=
        cpuVertexStrategicScore(
          vertexId,
          playerId
        )*1.25+
        7;
    }
  }

  for(const edgeId of vertex.edges){
    const edge=
      game.board.edges[edgeId];

    if(
      !edge ||
      edge.road!==null
    ){
      continue;
    }

    const farther=
      otherEnd(
        edgeId,
        vertexId
      );

    if(
      game.board.vertices[
        farther
      ]?.building
    ){
      continue;
    }

    score=
      Math.max(
        score,
        cpuVertexStrategicScore(
          farther,
          playerId
        )*.72
      );
  }

  return score;
}

function roadExpansionScore(
  edgeId,
  playerId
){
  const edge=
    game.board.edges[edgeId];

  if(!edge) return -9999;

  const player=
    playerById(playerId);

  let score=
    cpuRoadEndpointPotential(
      edge.a,
      playerId
    )+
    cpuRoadEndpointPotential(
      edge.b,
      playerId
    );

  const ownRoadAtA=
    game.board.vertices[
      edge.a
    ].edges.filter(
      otherEdgeId=>
        game.board.edges[
          otherEdgeId
        ].road===playerId
    ).length;

  const ownRoadAtB=
    game.board.vertices[
      edge.b
    ].edges.filter(
      otherEdgeId=>
        game.board.edges[
          otherEdgeId
        ].road===playerId
    ).length;

  /*
    既存道路網の端から外へ伸ばす街道を評価し、
    同じ場所で枝分かれしすぎるのを少し抑える。
  */
  if(ownRoadAtA===1){
    score+=5;
  }else if(ownRoadAtA>=2){
    score-=2;
  }

  if(ownRoadAtB===1){
    score+=5;
  }else if(ownRoadAtB>=2){
    score-=2;
  }

  const longestLeader=
    Math.max(
      ...game.players.map(
        other=>other.longestRoad||0
      )
    );

  if(
    player &&
    player.longestRoad>=3 &&
    player.longestRoad>=
      longestLeader-2
  ){
    score+=1.8;
  }

  score+=cpuStableTie(`road:${edgeId}:${playerId}`)*.025;

  return score;
}

function cpuBestRoadSequence(player,maxDepth=4){
  if(
    !player ||
    maxDepth<=0 ||
    player.pieces.road<=0
  ){
    return null;
  }

  const effectiveDepth=Math.min(
    maxDepth,
    cpuPlanningVP(player)>=7 ? 4 : 3
  );

  const roadStateSignature=[
    game.turnSerial,
    game.current,
    player.id,
    effectiveDepth,
    player.pieces.road,
    totalVP(player),
    victoryTarget(player),
    game.oldBootHolder??"none",
    ...game.players.map(other=>
      [
        other.id,
        other.roads.join("."),
        other.settlements.join("."),
        other.cities.join("."),
        other.hasLongestRoad?1:0,
      ].join(":")
    ),
  ].join("#");

  const cacheKey=
    `${player.id}:${effectiveDepth}`;

  const cached=
    cpuRoadSequenceCache.get(cacheKey);

  if(cached?.signature===roadStateSignature){
    return cached.value;
  }

  const opponentMaximum=Math.max(
    0,
    ...game.players
      .filter(other=>other.id!==player.id)
      .map(other=>other.longestRoad||0)
  );

  const currentHolder=
    game.players.find(
      other=>other.hasLongestRoad
    )||null;

  const limit=Math.min(
    effectiveDepth,
    player.pieces.road,
    4
  );

  let best=null;

  function inspect(sequence){
    if(!sequence.length) return;

    const projected=
      calculateLongestRoad(player.id);

    const wouldHold=
      projected>=5 &&
      (
        currentHolder?.id===player.id
          ?projected>=opponentMaximum
          :projected>opponentMaximum
      );

    const awardGain=
      wouldHold &&
      !player.hasLongestRoad
        ?2
        :0;

    const immediateWin=
      awardGain>0 &&
      cpuPlanningVP(player)+awardGain>=
        victoryTarget(player);

    const defenseValue=
      player.hasLongestRoad
        ?Math.max(
          0,
          projected-opponentMaximum
        )*8
        :0;

    const score=
      (immediateWin?1200:0)+
      awardGain*240+
      (wouldHold?42:0)+
      projected*13+
      defenseValue-
      sequence.length*18;

    if(
      !best ||
      score>best.score+.001 ||
      (
        Math.abs(score-best.score)<=.001 &&
        sequence.length<best.sequence.length
      )
    ){
      best={
        sequence:[...sequence],
        projectedLongest:projected,
        wouldHold,
        awardGain,
        immediateWin,
        score,
      };
    }
  }

  function dfs(sequence,depth){
    inspect(sequence);

    if(depth>=limit) return;

    let candidates=
      Object.keys(game.board.edges)
        .filter(edgeId=>
          canPlaceRoad(
            player.id,
            edgeId
          )
        )
        .map(edgeId=>{
          const edge=game.board.edges[edgeId];
          edge.road=player.id;
          player.roads.push(edgeId);

          let projected=0;
          try{
            projected=
              calculateLongestRoad(player.id);
          }finally{
            player.roads.pop();
            edge.road=null;
          }

          const wouldHold=
            projected>=5 &&
            (
              currentHolder?.id===player.id
                ?projected>=opponentMaximum
                :projected>opponentMaximum
            );

          const expansionValue=
            roadExpansionScore(
              edgeId,
              player.id
            );

          return {
            edgeId,
            projected,
            searchScore:
              projected*36+
              (wouldHold?220:0)+
              expansionValue*.42,
          };
        });

    candidates.sort((a,b)=>{
      if(
        Math.abs(
          b.searchScore-
          a.searchScore
        )>.001
      ){
        return b.searchScore-a.searchScore;
      }

      return String(a.edgeId).localeCompare(
        String(b.edgeId)
      );
    });

    /*
      道路だけは組合せが爆発しやすいので、各深さで上位6枝。
      最長交易路の伸びを先に見て枝刈りするため、
      単なる開拓向け道路に偏らない。
    */
    candidates=candidates.slice(0,6);

    for(const candidate of candidates){
      const edgeId=candidate.edgeId;
      const edge=game.board.edges[edgeId];
      if(!edge || edge.road!==null) continue;

      edge.road=player.id;
      player.roads.push(edgeId);

      try{
        dfs(
          [...sequence,edgeId],
          depth+1
        );
      }finally{
        player.roads.pop();
        edge.road=null;
      }
    }
  }

  dfs([],0);

  cpuRoadSequenceCache.set(
    cacheKey,
    {
      signature:roadStateSignature,
      value:best,
    }
  );

  return best;
}

function cpuBestRoadTarget(player){
  const awardPlan=
    cpuBestRoadSequence(
      player,
      Math.min(4,player.pieces.road)
    );

  const opponentMaximum=Math.max(
    0,
    ...game.players
      .filter(other=>other.id!==player.id)
      .map(other=>other.longestRoad||0)
  );

  /*
    v1.55:
    最長交易路を取れる道路は評価するが、roadSequence内部の巨大な
    探索スコアをそのままboardScoreへ流さない。
    2VPの価値・必要本数・奪還リスクを正規化した値へ変換する。
  */
  if(
    awardPlan?.sequence?.length &&
    awardPlan.awardGain>0
  ){
    const length=awardPlan.sequence.length;
    const margin=
      (awardPlan.projectedLongest||0)-
      opponentMaximum;
    const reclaimPenalty=
      margin<=0?22:
      margin===1?12:0;
    const existingRoadPenalty=
      Math.max(0,player.roads.length-7)*4;

    if(
      awardPlan.immediateWin ||
      length<=2 ||
      cpuPlanningVP(player)>=8
    ){
      return {
        id:awardPlan.sequence[0],
        score:
          (awardPlan.immediateWin?170:62)+
          awardPlan.awardGain*20-
          Math.max(0,length-1)*12-
          reclaimPenalty-
          existingRoadPenalty,
        awardGain:awardPlan.awardGain,
        roadAwardPlan:awardPlan,
      };
    }
  }

  /*
    開拓へつながる道路を、単なる道路王延長より先に検討する。
  */
  const expansion=
    cpuBestExpansionPlan(player);

  if(
    expansion?.nextRoadId &&
    canPlaceRoad(
      player.id,
      expansion.nextRoadId
    )
  ){
    return {
      id:expansion.nextRoadId,
      score:
        26+
        expansion.score-
        expansion.roadsNeeded*1.5,
      expansionTargetId:
        expansion.targetId,
      awardGain:0,
    };
  }

  /*
    既に最長交易路を保持している場合、僅差かつ終盤だけ1本道路で防衛。
    それ以外の「長くするだけ」の道路は候補から外す。
  */
  const defenseThreat=
    player.hasLongestRoad &&
    opponentMaximum>=
      (player.longestRoad||0)-1;

  if(
    defenseThreat &&
    cpuPlanningVP(player)>=8 &&
    awardPlan?.sequence?.length===1 &&
    awardPlan.projectedLongest>
      (player.longestRoad||0)
  ){
    return {
      id:awardPlan.sequence[0],
      score:46,
      awardGain:0,
      roadAwardPlan:awardPlan,
    };
  }

  const candidates=
    Object.keys(game.board.edges)
      .filter(edgeId=>
        canPlaceRoad(
          player.id,
          edgeId
        )
      );

  if(!candidates.length) return null;

  candidates.sort((a,b)=>{
    const diff=
      roadExpansionScore(
        b,
        player.id
      )-
      roadExpansionScore(
        a,
        player.id
      );

    if(Math.abs(diff)>.001){
      return diff;
    }

    return String(a).localeCompare(String(b));
  });

  return {
    id:candidates[0],
    score:
      Math.min(
        32,
        roadExpansionScore(
          candidates[0],
          player.id
        )*.35
      ),
    awardGain:0,
  };
}

function calculateLongestRoad(playerId){
  const owned=new Set(playerById(playerId).roads);
  let best=0;
  function dfs(vertexId,used){
    best=Math.max(best,used.size);
    const b=game.board.vertices[vertexId].building;
    if(used.size>0 && b && b.player!==playerId) return;
    for(const eid of game.board.vertices[vertexId].edges){
      if(!owned.has(eid)||used.has(eid)) continue;
      const next=otherEnd(eid,vertexId);
      used.add(eid); dfs(next,used); used.delete(eid);
    }
  }
  const starts=new Set();
  owned.forEach(eid=>{ const e=game.board.edges[eid]; starts.add(e.a); starts.add(e.b); });
  starts.forEach(v=>dfs(v,new Set()));
  return best;
}
function updateAwards(){
  const previousLongestRoadHolder=
    game.players.find(player=>player.hasLongestRoad)?.id??null;
  const previousLargestArmyHolder=
    game.players.find(player=>player.hasLargestArmy)?.id??null;

  game.players.forEach(
    player=>player.longestRoad=calculateLongestRoad(player.id)
  );

  const longestRoadMaximum=Math.max(
    ...game.players.map(player=>player.longestRoad)
  );
  const longestRoadLeaders=game.players.filter(
    player=>
      player.longestRoad===longestRoadMaximum &&
      longestRoadMaximum>=5
  );
  const previousLongestRoadPlayer=
    previousLongestRoadHolder===null
      ?null
      :playerById(previousLongestRoadHolder);

  game.players.forEach(
    player=>player.hasLongestRoad=false
  );

  if(longestRoadLeaders.length===1){
    longestRoadLeaders[0].hasLongestRoad=true;
  }else if(
    previousLongestRoadPlayer &&
    longestRoadLeaders.includes(previousLongestRoadPlayer)
  ){
    previousLongestRoadPlayer.hasLongestRoad=true;
  }

  const newLongestRoadHolder=
    game.players.find(player=>player.hasLongestRoad)?.id??null;

  const largestArmyMaximum=Math.max(
    ...game.players.map(player=>player.knightsPlayed)
  );
  const largestArmyLeaders=game.players.filter(
    player=>
      player.knightsPlayed===largestArmyMaximum &&
      largestArmyMaximum>=3
  );
  const previousLargestArmyPlayer=
    previousLargestArmyHolder===null
      ?null
      :playerById(previousLargestArmyHolder);

  game.players.forEach(
    player=>player.hasLargestArmy=false
  );

  if(largestArmyLeaders.length===1){
    largestArmyLeaders[0].hasLargestArmy=true;
  }else if(
    previousLargestArmyPlayer &&
    largestArmyLeaders.includes(previousLargestArmyPlayer)
  ){
    previousLargestArmyPlayer.hasLargestArmy=true;
  }

  const newLargestArmyHolder=
    game.players.find(player=>player.hasLargestArmy)?.id??null;

  if(
    newLongestRoadHolder!==null &&
    newLongestRoadHolder!==previousLongestRoadHolder
  ){
    queueAwardEvent("longestRoad",newLongestRoadHolder);
  }

  if(
    newLargestArmyHolder!==null &&
    newLargestArmyHolder!==previousLargestArmyHolder
  ){
    queueAwardEvent("largestArmy",newLargestArmyHolder);
  }
}
function visibleVP(p){
  return p.settlements.length + p.cities.length*2 + (p.hasLongestRoad?2:0) + (p.hasLargestArmy?2:0);
}
function totalVP(p){ return visibleVP(p)+p.revealedVP; }
function victoryTarget(p){ return 10+(game?.fishermen&&game.oldBootHolder===p.id?1:0); }

function checkVictory(){
  updateAwards();
  const candidate=currentPlayer();
  if(candidate && totalVP(candidate)>=victoryTarget(candidate)){
    game.winner=candidate.id;
    $("overlayMessage").textContent=`${candidate.name}の勝利！\n${totalVP(candidate)}勝利点`;
    $("overlayMessage").classList.remove("hidden");
    log(`${candidate.name}が${totalVP(candidate)}勝利点で勝利しました。`);
    cpuAnalysisFinalizeMatch(candidate);
  }
}

function render(){
  if(!game) return;
  enforceResourceIntegrity();
  renderBoard();
  renderSide();
  renderLog();
  collectResourcePopEvents();
  collectTurnAnnouncementEvents();
  collectAwardAnnouncements();
  scheduleFinalResultIfNeeded();
  onlineAfterRender();
}

const BOARD_PING_DURATION_MS=3000;

function updatePingButtons(){
  const buttons=[
    $("desktopPingBtn"),
    $("mobilePingBtn"),
  ].filter(Boolean);

  for(const button of buttons){
    button.classList.toggle(
      "active",
      boardPingMode
    );
    button.setAttribute(
      "aria-pressed",
      boardPingMode?"true":"false"
    );
    button.textContent=
      boardPingMode
        ?"📍場所を選択"
        :"📍ピン";
  }

  $("board")?.classList.toggle(
    "ping-mode",
    boardPingMode
  );
}

function toggleBoardPingMode(){
  if(!game || game.winner!==null) return;

  boardPingMode=!boardPingMode;
  updatePingButtons();

  if(
    boardPingMode &&
    typeof setMobileGameView==="function"
  ){
    setMobileGameView("board");
  }
}

function normalizedBoardPing(event){
  if(!event || typeof event!=="object") return null;

  const x=Number(event.x);
  const y=Number(event.y);

  if(!Number.isFinite(x) || !Number.isFinite(y)){
    return null;
  }

  return {
    id:
      String(
        event.id||
        `ping-${Date.now()}-${Math.random().toString(36).slice(2)}`
      ).slice(0,120),
    playerId:
      Number.isInteger(Number(event.playerId))
        ?Number(event.playerId)
        :null,
    playerName:
      String(event.playerName||"プレイヤー").slice(0,30),
    playerColor:
      String(event.playerColor||"#ffffff").slice(0,32),
    x,
    y,
    createdAt:
      Number(event.createdAt)||Date.now(),
  };
}

function acceptBoardPing(event,{renderNow=true}={}){
  const ping=normalizedBoardPing(event);
  if(!ping) return null;

  const existing=boardPingEvents.find(
    item=>item.id===ping.id
  );

  if(existing){
    return existing;
  }

  boardPingEvents.push(ping);
  boardPingEvents=boardPingEvents.slice(-32);

  if(renderNow && game){
    renderBoardPings();
  }

  return ping;
}

function queueBoardPing(x,y){
  if(!game) return null;

  const player=
    typeof localPlayer==="function"
      ?localPlayer()
      :game.players?.[0];

  if(!player) return null;

  const ping=acceptBoardPing({
    id:
      `ping-${player.id}-${Date.now()}-`+
      `${Math.random().toString(36).slice(2)}`,
    playerId:player.id,
    playerName:player.name,
    playerColor:player.color,
    x:Number(x),
    y:Number(y),
    createdAt:Date.now(),
  });

  if(
    ping &&
    typeof onlineSendBoardPing==="function"
  ){
    onlineSendBoardPing(ping);
  }

  return ping;
}

function receiveBoardPing(event){
  if(!game) return;
  acceptBoardPing(event,{renderNow:true});
}

function activeBoardPings(){
  const now=Date.now();

  boardPingEvents=boardPingEvents.filter(event=>{
    const age=now-Number(event?.createdAt||0);

    return (
      event &&
      Number.isFinite(Number(event.x)) &&
      Number.isFinite(Number(event.y)) &&
      age>=-1500 &&
      age<BOARD_PING_DURATION_MS
    );
  });

  return boardPingEvents;
}

function boardPingAlreadyRendered(id){
  return [...svg.querySelectorAll(".board-ping")]
    .some(element=>element.dataset.pingId===id);
}

function renderBoardPings(){
  const events=activeBoardPings();

  for(const event of events){
    if(boardPingAlreadyRendered(event.id)){
      continue;
    }

    const group=createSvg("g",{
      class:"board-ping",
      "data-ping-id":event.id||"",
    });

    const outer=createSvg("circle",{
      cx:event.x,
      cy:event.y,
      r:31,
      class:"board-ping-ring board-ping-ring-outer",
      stroke:event.playerColor||"#ffffff",
    });

    const inner=createSvg("circle",{
      cx:event.x,
      cy:event.y,
      r:13,
      class:"board-ping-ring board-ping-ring-inner",
      stroke:event.playerColor||"#ffffff",
    });

    const pin=createSvg("text",{
      x:event.x,
      y:event.y-8,
      class:"board-ping-icon",
    });
    pin.textContent="📍";

    const label=createSvg("text",{
      x:event.x,
      y:event.y+34,
      class:"board-ping-label",
      fill:event.playerColor||"#ffffff",
    });
    label.textContent=event.playerName||"プレイヤー";

    group.appendChild(outer);
    group.appendChild(inner);
    group.appendChild(pin);
    group.appendChild(label);
    svg.appendChild(group);

    const remaining=Math.max(
      40,
      BOARD_PING_DURATION_MS-
      (Date.now()-Number(event.createdAt||0))
    );

    setTimeout(()=>{
      const selector=
        `[data-ping-id="${CSS.escape(event.id||"")}"]`;
      svg.querySelector(selector)?.remove();
    },remaining);
  }
}

function handleBoardPingPointer(event){
  if(!boardPingMode || !game) return false;

  const ctm=svg.getScreenCTM();
  if(!ctm) return false;

  event.preventDefault();
  event.stopPropagation();
  event.stopImmediatePropagation();

  const point=svg.createSVGPoint();
  point.x=event.clientX;
  point.y=event.clientY;

  const localPoint=
    point.matrixTransform(ctm.inverse());

  queueBoardPing(localPoint.x,localPoint.y);

  boardPingMode=false;
  updatePingButtons();
  renderBoardPings();

  return true;
}

function openDesktopLog(){
  renderLog();
  $("desktopLogModal")?.classList.remove("hidden");
}

function closeDesktopLog(){
  $("desktopLogModal")?.classList.add("hidden");
}

function bindRobberHexTarget(element,hexId){
  if(
    !element ||
    game.phase!=="moveRobber" ||
    !isLocalTurn()
  ){
    return;
  }

  element.classList.add("robber-click-target");

  element.addEventListener("click",event=>{
    event.preventDefault();
    event.stopPropagation();

    if(hexId===game.robberHex) return;

    requestPlacementConfirmation({
      kind:"robber",
      targetId:hexId,
      itemName:"盗賊",
      guide:"盗賊をこのタイルへ移動します。",
      onConfirm:()=>{
        const player=currentPlayer();

        if(
          game.phase!=="moveRobber" ||
          !isLocalPlayer(player) ||
          hexId===game.robberHex
        ){
          log("そのタイルには移動できなくなりました。");
          render();
          return;
        }

        moveRobberTo(
          hexId,
          player.id
        );
      },
    });
  });
}

function renderBoard(){
  const renderGeneration=++boardRenderGeneration;
  const boardWrap=svg.parentElement;
  let boardSnapshot=boardWrap?.querySelector(".board-snapshot");

  // すでに完成済みの盤面がある場合、新しい画像が読み終わるまで上に残す。
  // 通信更新が連続した場合は、最初の完成済みスナップショットを使い続ける。
  if(!boardSnapshot && svg.childElementCount>0 && boardWrap){
    boardSnapshot=svg.cloneNode(true);
    boardSnapshot.removeAttribute("id");
    boardSnapshot.classList.add("board-snapshot");
    boardSnapshot.setAttribute("aria-hidden","true");
    boardWrap.insertBefore(boardSnapshot,$("resourcePopLayer"));
  }

  let pendingTileImages=0;
  let boardBuildFinished=false;

  const releaseBoardSnapshot=()=>{
    if(
      !boardBuildFinished ||
      pendingTileImages>0 ||
      renderGeneration!==boardRenderGeneration
    ){
      return;
    }

    requestAnimationFrame(()=>{
      if(renderGeneration===boardRenderGeneration){
        boardWrap?.querySelector(".board-snapshot")?.remove();
      }
    });
  };

  svg.innerHTML="";
  svg.setAttribute("viewBox",game.board.large?"35 -48 870 805":"-10 -72 920 850");
  const defs=createSvg("defs");
  svg.appendChild(defs);
  svg.appendChild(createSvg("rect",{x:-100,y:-100,width:1120,height:1000,fill:"#57acd1"}));
  const tokenRadius=game.board.large?21:25;
  const numberSize=game.board.large?20:23;
  for(const h of game.board.hexes){
    const pts=h.corners.map(v=>`${game.board.vertices[v].x},${game.board.vertices[v].y}`).join(" ");
    const poly=createSvg("polygon",{points:pts,class:`hex tile-${h.resource}`});
    if(game.phase==="moveRobber" && isLocalTurn()){
      poly.classList.add("robber-target");
      bindRobberHexTarget(poly,h.id);
    }
    svg.appendChild(poly);

    const clipId=`tile-clip-${h.id}`;
    const clip=createSvg("clipPath",{id:clipId});
    clip.appendChild(createSvg("polygon",{points:pts}));
    defs.appendChild(clip);
    const tileImage=createSvg("image",{
      x:h.x-game.board.size*Math.sqrt(3)/2,
      y:h.y-game.board.size,
      width:game.board.size*Math.sqrt(3),
      height:game.board.size*2,
      preserveAspectRatio:"xMidYMid slice",
      class:"tile-image",
      "clip-path":`url(#${clipId})`
    });

    pendingTileImages++;
    let triedPng=false;
    let imageFinished=false;

    const finishTileImage=()=>{
      if(imageFinished) return;
      imageFinished=true;
      pendingTileImages=Math.max(0,pendingTileImages-1);
      releaseBoardSnapshot();
    };

    tileImage.addEventListener("load",finishTileImage,{once:true});
    tileImage.addEventListener("error",()=>{
      if(!triedPng){
        triedPng=true;
        tileImage.setAttribute(
          "href",
          `${TILE_IMAGE_PATH}/${h.resource}.png`
        );
      }else{
        tileImage.remove();
        finishTileImage();
      }
    });

    svg.appendChild(tileImage);
    tileImage.setAttribute(
      "href",
      `${TILE_IMAGE_PATH}/${h.resource}.webp`
    );

    // 画像より前の枠線が隠れないよう、境界線を最後に重ねる
    svg.appendChild(createSvg("polygon",{points:pts,class:"hex-border"}));

    if(h.resource==="lake"){
      const nums=h.lakeNumbers||[];
      const positions=nums.length===4?[[-18,-18],[18,-18],[-18,18],[18,18]]:[[-20,0],[20,0]];
      nums.forEach((num,i)=>{
        const [ox,oy]=positions[i];

        const lakeToken=createSvg("circle",{
          cx:h.x+ox,
          cy:h.y+oy,
          r:game.board.large?14:16,
          class:"lake-number",
        });
        bindRobberHexTarget(lakeToken,h.id);
        svg.appendChild(lakeToken);

        const lakeText=createSvg("text",{
          x:h.x+ox,
          y:h.y+oy+1,
          class:"lake-number-text",
          style:`font-size:${game.board.large?13:15}px`,
        });
        lakeText.textContent=num;
        bindRobberHexTarget(lakeText,h.id);
        svg.appendChild(lakeText);
      });

      const fish=createSvg("text",{
        x:h.x,
        y:h.y+(nums.length===4?0:28),
        class:"fishing-ground-fish",
        style:`font-size:${game.board.large?18:22}px`,
      });
      fish.textContent="🐟";
      bindRobberHexTarget(fish,h.id);
      svg.appendChild(fish);
    }else if(h.number){
      const numberToken=createSvg("circle",{
        cx:h.x,
        cy:h.y,
        r:tokenRadius,
        class:"number-token",
      });
      bindRobberHexTarget(numberToken,h.id);
      svg.appendChild(numberToken);

      const numberText=createSvg("text",{
        x:h.x,
        y:h.y-3,
        class:
          `number-text `+
          `${[6,8].includes(h.number)?"hot-number":""}`,
        style:`font-size:${numberSize}px`,
      });
      numberText.textContent=h.number;
      bindRobberHexTarget(numberText,h.id);
      svg.appendChild(numberText);

      const pipText=createSvg("text",{
        x:h.x,
        y:h.y+(game.board.large?14:17),
        class:"pip-text",
      });
      pipText.textContent="•".repeat(PIPS[h.number]);
      bindRobberHexTarget(pipText,h.id);
      svg.appendChild(pipText);
    }
    if(game.robberHex===h.id){
      const cat=createSvg("text",{x:h.x,y:h.y+7,class:"robber-cat",style:`font-size:${game.board.large?34:42}px`});
      cat.textContent="🐱";
      svg.appendChild(cat);
    }

    if(placementPreviewMatches("robber",h.id)){
      svg.appendChild(
        createSvg("polygon",{
          points:pts,
          class:"placement-preview-hex",
        })
      );

      const previewRobber=createSvg("text",{
        x:h.x,
        y:h.y+7,
        class:"placement-preview-robber",
        style:`font-size:${game.board.large?34:42}px`,
      });
      previewRobber.textContent="🐱";
      svg.appendChild(previewRobber);
    }
  }

  // 港はタイルより後に描画し、白いタイル境界で線が隠れないようにする
  const harborOffset=game.board.large?55:68;
  const harborRadius=game.board.large?20:24;
  const harborLineStartOffset=game.board.large?6:8;
  const harborLayer=createSvg("g",{class:"harbor-layer"});
  for(const eid of game.board.harbors){
    const e=game.board.edges[eid], a=game.board.vertices[e.a], b=game.board.vertices[e.b];
    const mx=(a.x+b.x)/2,my=(a.y+b.y)/2;
    let dx=mx-game.board.cx,dy=my-game.board.cy;
    const len=Math.hypot(dx,dy)||1;
    dx/=len;
    dy/=len;

    const lx=mx+dx*harborOffset,ly=my+dy*harborOffset;
    const aStartX=a.x+dx*harborLineStartOffset;
    const aStartY=a.y+dy*harborLineStartOffset;
    const bStartX=b.x+dx*harborLineStartOffset;
    const bStartY=b.y+dy*harborLineStartOffset;

    harborLayer.appendChild(createSvg("line",{
      x1:aStartX,y1:aStartY,x2:lx,y2:ly,class:"harbor-line"
    }));
    harborLayer.appendChild(createSvg("line",{
      x1:bStartX,y1:bStartY,x2:lx,y2:ly,class:"harbor-line"
    }));
    harborLayer.appendChild(createSvg("circle",{
      cx:lx,cy:ly,r:harborRadius,class:"harbor-label"
    }));
    const text=createSvg("text",{x:lx,y:ly,class:"harbor-text"});
    text.textContent=e.harbor==="3:1"?"3:1":`${RESOURCE_ICON[e.harbor]}2:1`;
    harborLayer.appendChild(text);
  }
  svg.appendChild(harborLayer);

  if(game.fishermen){
    const fishingLayer=createSvg("g",{class:"fishing-ground-layer"});
    for(const ground of game.board.fishingGrounds){
      const v=game.board.vertices[ground.vertexId];
      let dx=v.x-game.board.cx,dy=v.y-game.board.cy;
      const len=Math.hypot(dx,dy)||1; dx/=len; dy/=len;
      const px=-dy,py=dx;
      const scale=game.board.large?.82:1;
      const innerX=v.x+dx*3,innerY=v.y+dy*3;
      const side=22*scale,out=55*scale,mid=20*scale;
      const points=[
        `${innerX},${innerY}`,
        `${v.x+dx*mid+px*side},${v.y+dy*mid+py*side}`,
        `${v.x+dx*out},${v.y+dy*out}`,
        `${v.x+dx*mid-px*side},${v.y+dy*mid-py*side}`
      ].join(" ");
      fishingLayer.appendChild(createSvg("polygon",{points,class:"fishing-ground-tile"}));
      const bx=v.x+dx*(35*scale),by=v.y+dy*(35*scale);
      fishingLayer.appendChild(createSvg("circle",{cx:bx,cy:by,r:15*scale,class:"fishing-ground-badge"}));
      const text=createSvg("text",{x:bx,y:by-2*scale,class:"fishing-ground-number",style:`font-size:${15*scale}px`});
      text.textContent=ground.number; fishingLayer.appendChild(text);
      const fish=createSvg("text",{x:bx,y:by+12*scale,class:"fishing-ground-fish",style:`font-size:${9*scale}px`});
      fish.textContent="🐟"; fishingLayer.appendChild(fish);
    }
    svg.appendChild(fishingLayer);
  }

  for(const e of Object.values(game.board.edges)){
    const a=game.board.vertices[e.a],b=game.board.vertices[e.b];
    if(e.road!==null){
      svg.appendChild(createSvg("line",{x1:a.x,y1:a.y,x2:b.x,y2:b.y,class:"road",stroke:playerById(e.road).color}));
    }

    if(placementPreviewMatches("road",e.id)){
      svg.appendChild(
        createSvg("line",{
          x1:a.x,
          y1:a.y,
          x2:b.x,
          y2:b.y,
          class:"placement-preview-road",
          stroke:
            pendingPlacementPreview?.playerColor||
            currentPlayer()?.color||
            "#ffffff",
        })
      );
    }

    const click=createSvg("line",{x1:a.x,y1:a.y,x2:b.x,y2:b.y,class:"edge-click"});
    click.addEventListener("click",()=>{
      if(game.phase==="setupRoad") setupClickEdge(e.id);
      else normalClickEdge(e.id);
    });
    svg.appendChild(click);
  }
  const buildingScale=game.board.large?.82:1;
  for(const v of Object.values(game.board.vertices)){
    if(v.building){
      const p=playerById(v.building.player);
      if(v.building.type==="settlement"){
        const a=12*buildingScale,b=11*buildingScale,c=2*buildingScale,d=14*buildingScale;
        const pts=`${v.x-a},${v.y+b} ${v.x-a},${v.y-c} ${v.x},${v.y-d} ${v.x+a},${v.y-c} ${v.x+a},${v.y+b}`;
        svg.appendChild(createSvg("polygon",{points:pts,class:"settlement",fill:p.color}));
      }else{
        const a=16*buildingScale,b=13*buildingScale,c=7*buildingScale,d=5*buildingScale,e=16*buildingScale,f=6*buildingScale,g=4*buildingScale;
        const pts=`${v.x-a},${v.y+b} ${v.x-a},${v.y-c} ${v.x-d},${v.y-c} ${v.x-d},${v.y-e} ${v.x+f},${v.y-e} ${v.x+f},${v.y-g} ${v.x+a},${v.y-g} ${v.x+a},${v.y+b}`;
        svg.appendChild(createSvg("polygon",{points:pts,class:"city",fill:p.color}));
      }
    }
    if(
      placementPreviewMatches("settlement",v.id) ||
      placementPreviewMatches("city",v.id)
    ){
      const previewKind=
        pendingPlacementPreview?.kind||
        "settlement";

      const previewMarker=createSvg("circle",{
        cx:v.x,
        cy:v.y,
        r:
          previewKind==="city"
            ?(game.board.large?19:23)
            :(game.board.large?15:18),
        class:
          `placement-preview-vertex `+
          `placement-preview-${previewKind}`,
        fill:
          pendingPlacementPreview?.playerColor||
          currentPlayer()?.color||
          "#ffffff",
      });

      svg.appendChild(previewMarker);
    }

    const hit=createSvg("circle",{cx:v.x,cy:v.y,r:game.board.large?11:14,class:"vertex-click"});
    hit.addEventListener("click",()=>{
      if(game.phase==="setupSettlement") setupClickVertex(v.id);
      else normalClickVertex(v.id);
    });
    svg.appendChild(hit);
  }

  renderBoardPings();

  boardBuildFinished=true;
  applyMobileBoardCrop();
  updatePingButtons();
  releaseBoardSnapshot();

  // 読み込みイベントが返らない特殊な環境でも、永久に覆わないための保険。
  setTimeout(()=>{
    if(renderGeneration===boardRenderGeneration){
      boardWrap?.querySelector(".board-snapshot")?.remove();
    }
  },2000);
}

function resolveOnlineTrade(accepted){
  const trade=game?.pendingTrade;

  if(!trade || trade.toId!==localPlayerId()){
    return;
  }

  if(tradeWasResolved(trade.id)){
    game.pendingTrade=null;
    shownPendingTradeId=null;
    closeChoiceModal();
    render();
    return;
  }

  const from=playerById(trade.fromId);
  const to=playerById(trade.toId);
  const valid=canExecutePlayerTrade(
    from,
    to,
    trade.give,
    trade.get
  );

  cpuAnalysisQueueHumanReceipt(
    to,
    "player_trade_response",
    {
      fromId:from?.id??null,
      fromName:from?.name??null,
      accepted:!!accepted,
      valid:!!valid,
      give:cpuAnalysisClone(trade.give),
      get:cpuAnalysisClone(trade.get),
    }
  );

  game.pendingTrade=null;
  shownPendingTradeId=null;

  let completed=false;

  if(accepted && valid){
    completed=executePlayerTrade(
      to,
      trade.give,
      trade.get,
      from,
      trade.id
    );
  }else{
    rememberResolvedTrade(trade.id);
  }

  if(completed){
    log(
      `${to.name}が${from.name}からの交易提案に`+
      `YESと回答しました。`
    );
  }else if(accepted && !valid){
    log(
      `${to.name}は要求された資源を持っていないため、`+
      `交易を承諾できませんでした。`
    );
  }else{
    log(
      `${to.name}が${from.name}からの交易提案に`+
      `NOと回答しました。`
    );
  }

  closeChoiceModal();
  render();
}

function handleOnlinePendingUI(){
  if(!ONLINE_MODE || !game) return;
  const local=localPlayer();
  if(!local) return;

  if(game.phase==="discard" && game.discardPlayerId===local.id && !discardSelection){
    openDiscardModal(local,Math.floor(totalResources(local)/2));
    return;
  }

  if(game.phase==="fishSwap" && game.fishSwapPlayerId===local.id){
    openPendingFishSwapModal(local);
    return;
  }

  const trade=game.pendingTrade;

  if(!trade){
    shownPendingTradeId=null;
    return;
  }

  if(tradeWasResolved(trade.id)){
    game.pendingTrade=null;
    shownPendingTradeId=null;
    render();
    return;
  }

  if(trade.toId===local.id && shownPendingTradeId!==trade.id){
    shownPendingTradeId=trade.id;

    const from=playerById(trade.fromId);
    const canAccept=canExecutePlayerTrade(
      from,
      local,
      trade.give,
      trade.get
    );

    const guide=
      `受け取る：${tradeResourceText(trade.give)} ／ `+
      `渡す：${tradeResourceText(trade.get)}`+
      (canAccept
        ?""
        :"／要求された資源が不足しているためYESは選べません。");

    openChoiceModal({
      title:`${from.name}から交易提案`,
      guide,
      options:[
        {
          value:true,
          label:"YES",
          icon:"✓",
          className:"yes",
          disabled:!canAccept,
          sub:canAccept?"交易を成立させる":"必要な資源が不足",
        },
        {
          value:false,
          label:"NO",
          icon:"×",
          className:"no",
        },
      ],
      allowCancel:false,
      onSelect:accepted=>{
        shownPendingTradeId=null;
        resolveOnlineTrade(accepted);
      },
    });
  }
}

function renderFishPanel(){
  const panel=$("fishPanel");
  if(!panel || !game) return;
  panel.classList.toggle("hidden",!game.fishermen);
  if(!game.fishermen) return;
  const human=localPlayer(),cp=currentPlayer();
  const holder=game.oldBootHolder===null?"なし":playerById(game.oldBootHolder).name;
  $("fishStatus").textContent=`魚チップ ${human.fishTokens.length}/7枚（合計${fishTotal(human)}匹）｜山札 ${game.fishSupply.length}枚｜ボロ靴：${holder}`;
  $("fishTokens").innerHTML=human.fishTokens.length?human.fishTokens.map((v,i)=>`<button class="fish-token ${game.selectedFishIndices.includes(i)?"selected":""}" data-fish-index="${i}">🐟×${v}</button>`).join(""):"<small>魚チップなし</small>";
  document.querySelectorAll("[data-fish-index]").forEach(b=>b.addEventListener("click",()=>toggleFishToken(Number(b.dataset.fishIndex))));
  $("fishSelectedTotal").textContent=`選択：${selectedFishTotal()}匹`;
  $("fishClearBtn").disabled=!game.selectedFishIndices.length;
  const canAct=isLocalTurn()&&game.phase==="turn"&&!game.winner&&!game.diceRolling&&game.freeRoads===0;
  document.querySelectorAll("[data-fish-action]").forEach(b=>{
    const action=b.dataset.fishAction,cost=FISH_ACTION_COST[action];
    let valid=!!findFishPayment(human.fishTokens,cost);
    if(action==="removeRobber") valid=valid&&game.robberHex!==null;
    if(action==="steal") valid=valid&&game.players.some(p=>p.id!==localPlayerId()&&totalResources(p)>0);
    if(action==="resource") valid=valid&&RESOURCES.some(r=>game.bank[r]>0);
    if(action==="road") valid=valid&&human.pieces.road>0&&Object.keys(game.board.edges).some(e=>canPlaceRoad(localPlayerId(),e));
    if(action==="dev") valid=valid&&game.devDeck.length>0;
    b.disabled=!canAct||!valid;
  });
  $("bootTransferBtn").disabled=!canAct||game.oldBootHolder!==localPlayerId()||!eligibleBootRecipients(human).length;
}

function fitFishermenPlayerDetails(){
  const playersElement=$("players");
  if(!playersElement) return;

  const details=[
    ...playersElement.querySelectorAll(".player-card-details"),
  ];

  for(const detail of details){
    detail.style.removeProperty("font-size");
    detail.style.removeProperty("letter-spacing");
    detail.style.removeProperty("transform");
    detail.style.removeProperty("transform-origin");

    if(!game?.fishermen){
      continue;
    }

    /*
      漁師拡張では項目が1つ増えるため、
      まず文字を少し小さくし、それでも入らない場合だけ
      横方向をわずかに縮めて全項目を残す。
    */
    let fontSize=8.5;
    detail.style.fontSize=`${fontSize}px`;
    detail.style.letterSpacing="-0.03em";

    while(
      detail.scrollWidth>detail.clientWidth &&
      fontSize>6.75
    ){
      fontSize-=0.25;
      detail.style.fontSize=`${fontSize}px`;
    }

    if(
      detail.clientWidth>0 &&
      detail.scrollWidth>detail.clientWidth
    ){
      const scale=Math.max(
        0.72,
        Math.min(
          1,
          detail.clientWidth/detail.scrollWidth
        )
      );

      detail.style.transformOrigin="left center";
      detail.style.transform=`scaleX(${scale})`;
    }
  }
}

function renderSide(){
  const human=localPlayer(), cp=currentPlayer();
  renderFishPanel();
  $("turnTitle").textContent=game.winner!==null?"ゲーム終了":`${cp.name}のターン`;
  let phase="";
  if(game.phase==="setupSettlement") phase=`初期配置 ${game.setupRound}/2：${cp.name}が開拓地を置きます。`;
  else if(game.phase==="setupRoad") phase=`初期配置 ${game.setupRound}/2：初期街道を置きます。`;
  else if(game.phase==="discard") phase=`資源を半分捨てる処理中です。`;
  else if(game.phase==="moveRobber") phase=`🐱を移動する土地を選びます。`;
  else if(game.phase==="chooseVictim") phase=`資源を奪う相手を選択してください。`;
  else if(game.phase==="fishSwap") phase=`魚チップの引き直し処理中です。`;
  else if(game.diceRolling) phase=`ダイスを振っています……`;
  else if(!game.rolled) phase=`ダイスを振ってください。`;
  else if(game.freeRoads>0) phase=`無料の街道をあと${game.freeRoads}本置いてください。`;
  else if(game.buildMode) phase=`${{road:"街道",settlement:"開拓地",city:"都市"}[game.buildMode]}の建設場所を選択中。`;
  else if(cp.builtThisTurn) phase=`このターンの建設は完了しています。交易・発展カード使用後、ターン終了できます。`;
  else phase=`建設はこのターンに1回だけ行えます。交易・発展カード使用後、ターン終了できます。`;
  $("phaseText").textContent=phase;
  updateMobileGameSummary(
    game.winner!==null?"ゲーム終了":`${cp.name}のターン`,
    phase,
    human
  );
  const persistentDice=
    game.rolled && Array.isArray(game.turnDice)
      ?game.turnDice
      :game.dice;

  $("die1").textContent=persistentDice?.[0]||"–";
  $("die2").textContent=persistentDice?.[1]||"–";
  $("rollBtn").disabled=!isLocalTurn()||game.phase!=="turn"||game.rolled||game.winner!==null||game.diceRolling;
  $("endTurnBtn").disabled=!isLocalTurn()||game.phase!=="turn"||!game.rolled||game.freeRoads>0||game.winner!==null||game.diceRolling;

  $("resourceCards").innerHTML=RESOURCES.map(resource=>{
    const ownCount=Math.max(0,human.resources[resource]);
    const bankCount=String(
      Math.max(0,game.bank[resource])
    ).padStart(2,"0");

    return `<div class="resource-stock-column">
      <div class="resource ${resource}">
        <span class="resource-name">${RESOURCE_ICON[resource]} ${RESOURCE_JA[resource]}</span>
        <b>${ownCount}</b>
      </div>
      <span class="resource-bank-stock">在庫${bankCount}</span>
    </div>`;
  }).join("");
  $("pieceCounts").innerHTML=`<span>街道駒 ${human.pieces.road}</span><span>開拓地駒 ${human.pieces.settlement}</span><span>都市駒 ${human.pieces.city}</span><span>資源計 ${totalResources(human)}</span><span>発展山札 ${game.devDeck.length}</span>`;
  document.querySelectorAll("[data-action]").forEach(b=>{
    b.classList.toggle("active",game.buildMode===b.dataset.action);
    b.disabled=!isLocalTurn() || game.phase!=="turn" || !game.rolled || game.winner!==null || cp.builtThisTurn;
  });

  const devNames={knight:"騎士",roadBuilding:"街道建設",yearOfPlenty:"発見",monopoly:"独占",vp:"勝利点"};
  const counts={};
  human.dev.forEach(c=>counts[c]=(counts[c]||0)+1);
  $("devCards").innerHTML=Object.keys(devNames).map(c=>{
    const n=counts[c]||0;
    const can=n>0 && usableDevCount(human,c)>0 && isLocalTurn() && game.phase==="turn";
    const label=c==="vp"?"公開":"使う";
    return `<div class="dev-row"><span>${devNames[c]}：${n}</span><button data-dev="${c}" ${can?"":"disabled"}>${label}</button></div>`;
  }).join("");
  document.querySelectorAll("[data-dev]").forEach(b=>b.addEventListener("click",()=>playDev(b.dataset.dev)));

  const playersElement=$("players");
  playersElement.classList.toggle(
    "fishermen-player-list",
    !!game.fishermen
  );

  playersElement.innerHTML=game.players.map(player=>{
    const awards=[
      player.hasLongestRoad?"最長交易路":null,
      player.hasLargestArmy?"最大騎士団":null,
    ].filter(Boolean).join("・");

    const victoryPoints=publicVP(player);

    const detailItems=[
      `資源${totalResources(player)}`,
      `発展${player.dev.length}`,
      ...(game.fishermen?[`魚${player.fishTokens.length}枚`]:[]),
      `勝利点${Math.max(0,player.revealedVP)}`,
      `騎士${player.knightsPlayed}`,
      `最長${player.longestRoad}`,
      ...(awards?[awards]:[]),
    ];

    return `<div class="player-card ${player.id===game.current?"current":""}">
      <span class="player-dot" style="background:${player.color}"></span>

      <div class="player-card-main">
        <div class="player-card-name-row">
          <span class="player-card-name">
            ${player.name}
            ${game.fishermen&&game.oldBootHolder===player.id
              ?'<span class="boot-mark">ボロ靴</span>'
              :""
            }
          </span>
        </div>

        <div class="player-card-detail-row">
          <small class="player-card-details">
            ${detailItems.join(" / ")}
          </small>

          <b class="player-victory-points">
            ${victoryPoints}/${victoryTarget(player)}点
          </b>
        </div>
      </div>
    </div>`;
  }).join("");

  fitFishermenPlayerDetails();

  $("cpuTradeBtn").disabled=!isLocalTurn()||game.phase!=="turn"||!game.rolled||!!game.pendingTrade;

  const finished=game.winner!==null;
  const resultButtonText=finished
    ?"最終リザルトを見る"
    :"途中経過を見る";

  $("resultBtn").textContent=resultButtonText;

  const desktopResultButton=$("desktopResultBtn");
  if(desktopResultButton){
    desktopResultButton.textContent=resultButtonText;
  }

  $("resultPanelGuide").textContent=finished
    ?"最終順位とゲーム全体のダイス結果を確認できます。"
    :"途中経過ではダイスの出目だけ確認できます。";

  updateTradeRate();
}

let mobileGameView="board";

const MOBILE_BOARD_CROP = {
  xStart:1,

  /*
    右端の港枠まで表示するため、
    スマホ版は右側だけ切り抜かない。
  */
  xEnd:20,

  yStart:3,
  yEnd:17,
  divisions:20,
};

function mobileBoardCropInset(){
  return {
    left:(MOBILE_BOARD_CROP.xStart/MOBILE_BOARD_CROP.divisions)*100,
    right:(
      (MOBILE_BOARD_CROP.divisions-MOBILE_BOARD_CROP.xEnd) /
      MOBILE_BOARD_CROP.divisions
    )*100,
    top:(MOBILE_BOARD_CROP.yStart/MOBILE_BOARD_CROP.divisions)*100,
    bottom:(
      (MOBILE_BOARD_CROP.divisions-MOBILE_BOARD_CROP.yEnd) /
      MOBILE_BOARD_CROP.divisions
    )*100,
  };
}

function shouldCropMobileBoard(){
  return window.matchMedia(
    "(max-width: 720px), " +
    "(max-width: 950px) and (max-height: 520px) and (orientation: landscape)"
  ).matches;
}

function applyMobileBoardCrop(){
  /*
    縦持ちタブレットはスマホ式タブUIを使うが、
    スマホ向けのX1-X20・Y3-Y17切り取りは適用しない。
  */
  const shouldCrop=shouldCropMobileBoard();

  const targets=[
    $("board"),
    ...document.querySelectorAll(".board-snapshot"),
  ].filter(Boolean);

  const inset=mobileBoardCropInset();
  const clipValue=
    `inset(${inset.top}% ${inset.right}% `+
    `${inset.bottom}% ${inset.left}%)`;

  for(const target of targets){
    // v1.17の拡大を完全に解除する
    target.style.removeProperty("transform");
    target.style.removeProperty("transform-origin");

    if(shouldCrop){
      target.style.setProperty("clip-path",clipValue);
      target.style.setProperty("-webkit-clip-path",clipValue);
    }else{
      target.style.removeProperty("clip-path");
      target.style.removeProperty("-webkit-clip-path");
    }
  }
}

function syncMobileTurnPanelPlacement(){
  const panel=document.querySelector(".turn-panel");
  const home=$("turnPanelHome");
  const boardWrap=document.querySelector(".board-wrap");
  if(!panel || !home || !boardWrap) return;

  const smartphone=
    typeof isSmartphoneGameViewport==="function"
      ?isSmartphoneGameViewport()
      :window.matchMedia("(max-width: 720px)").matches;

  const shouldMoveToBoard=
    smartphone &&
    document.body.classList.contains("online-game-mode");

  if(shouldMoveToBoard){
    if(panel.parentElement!==boardWrap){
      boardWrap.appendChild(panel);
    }
    panel.classList.add("mobile-board-turn-panel");
  }else{
    const homeParent=home.parentElement;
    if(homeParent && panel.parentElement!==homeParent){
      homeParent.insertBefore(panel,home.nextSibling);
    }
    panel.classList.remove("mobile-board-turn-panel");
  }
}

const DESKTOP_1080_WIDTH=1920;
const DESKTOP_1080_HEIGHT=1080;

function desktop1080FitAvailable(){
  const smartphone=
    typeof isSmartphoneGameViewport==="function"
      ?isSmartphoneGameViewport()
      :window.matchMedia(
        "(max-width: 720px)"
      ).matches;

  return !smartphone;
}

function updateDesktop1080Fit(){
  const stage=$("desktopFitStage");
  const button=$("desktop1080FitBtn");

  if(!stage || !button) return;

  const inGame=
    document.body.classList.contains(
      "online-game-mode"
    );

  const active=
    desktop1080FitEnabled &&
    inGame &&
    desktop1080FitAvailable();

  document.body.classList.toggle(
    "desktop-1080-fit",
    active
  );

  if(!active){
    stage.style.removeProperty(
      "--desktop-1080-scale"
    );
    stage.style.removeProperty("left");
    stage.style.removeProperty("top");

    button.classList.remove("active");
    button.textContent="1920×1080";
    button.title=
      "ゲーム画面を仮想1920×1080で"+
      "表示領域に合わせる";
    return;
  }

  const viewportWidth=
    Math.max(1,window.innerWidth);
  const viewportHeight=
    Math.max(1,window.innerHeight);

  const scale=Math.min(
    viewportWidth/DESKTOP_1080_WIDTH,
    viewportHeight/DESKTOP_1080_HEIGHT
  );

  const renderedWidth=
    DESKTOP_1080_WIDTH*scale;
  const renderedHeight=
    DESKTOP_1080_HEIGHT*scale;

  const left=
    Math.max(
      0,
      (viewportWidth-renderedWidth)/2
    );

  const top=
    Math.max(
      0,
      (viewportHeight-renderedHeight)/2
    );

  stage.style.setProperty(
    "--desktop-1080-scale",
    String(scale)
  );
  stage.style.left=`${left}px`;
  stage.style.top=`${top}px`;

  button.classList.add("active");
  button.textContent="通常表示";
  button.title=
    `1920×1080仮想表示：`+
    `${Math.round(scale*100)}%で縮小中`;
}

function toggleDesktop1080Fit(){
  desktop1080FitEnabled=
    !desktop1080FitEnabled;

  localStorage.setItem(
    DESKTOP_1080_FIT_STORAGE_KEY,
    desktop1080FitEnabled?"1":"0"
  );

  updateDesktop1080Fit();

  /*
    仮想解像度へ切り替えた直後に、
    盤面の切り抜き・配置を再計算する。
  */
  requestAnimationFrame(()=>{
    applyMobileBoardCrop();
    syncMobileTurnPanelPlacement();
    fitFishermenPlayerDetails();
  });
}

function setMobileGameView(view,scrollToTop=true){
  if(!["board","actions","info"].includes(view)){
    view="board";
  }

  mobileGameView=view;

  const main=$("gameMain");
  if(main){
    main.classList.remove(
      "mobile-view-board",
      "mobile-view-actions",
      "mobile-view-info"
    );
    main.classList.add(`mobile-view-${view}`);
  }

  document.querySelectorAll("[data-mobile-view]").forEach(button=>{
    const active=button.dataset.mobileView===view;
    button.classList.toggle("active",active);
    button.setAttribute("aria-selected",active?"true":"false");
  });

  applyMobileBoardCrop();
  syncMobileTurnPanelPlacement();

  if(
    scrollToTop &&
    (
      typeof isSmartphoneGameViewport==="function"
        ?isSmartphoneGameViewport()
        :window.matchMedia("(max-width: 720px)").matches
    )
  ){
    const aside=main?.querySelector("aside");
    if(aside) aside.scrollTop=0;
  }
}

function updateMobileGameSummary(turnText,phaseText,player){
  const turnSummary=$("mobileTurnSummary");
  const resourceSummary=$("mobileResourceSummary");

  if(turnSummary){
    const persistentDice=
      game?.rolled && Array.isArray(game.turnDice)
        ?game.turnDice
        :null;

    const diceText=
      persistentDice?.[0] && persistentDice?.[1]
        ?`｜🎲${persistentDice[0]}＋${persistentDice[1]}＝${persistentDice[0]+persistentDice[1]}`
        :"";

    turnSummary.textContent=
      `${turnText}${phaseText?`｜${phaseText}`:""}${diceText}`;
  }

  if(!resourceSummary || !player){
    return;
  }

  const resourceItems=RESOURCES.map(resource=>
    `<span class="mobile-status-item resource-status">
      <span class="mobile-status-icon">${RESOURCE_ICON[resource]}</span>
      <b>${Math.max(0,player.resources[resource])}</b>
    </span>`
  ).join("");

  const pieceItems=[
    {
      className:"road-status",
      icon:"🛣️",
      label:"街道",
      value:Math.max(0,player.pieces.road),
    },
    {
      className:"settlement-status",
      icon:"🏠",
      label:"開拓地",
      value:Math.max(0,player.pieces.settlement),
    },
    {
      className:"city-status",
      icon:"🏰",
      label:"都市",
      value:Math.max(0,player.pieces.city),
    },
    {
      className:"resource-total-status",
      icon:"📦",
      label:"資源計",
      value:Math.max(0,totalResources(player)),
    },
  ];

  if(game?.fishermen){
    pieceItems.push({
      className:"fish-token-status",
      icon:"🐟",
      label:"魚チップ",
      value:`${Math.max(0,player.fishTokens.length)}/7`,
    });
  }

  const pieceHtml=pieceItems.map(item=>
    `<span class="mobile-status-item piece-status ${item.className}">
      <span class="mobile-status-icon">${item.icon}</span>
      <span class="mobile-status-label">${item.label}</span>
      <b>${item.value}</b>
    </span>`
  ).join("");

  resourceSummary.innerHTML=
    `<div class="mobile-resource-counts">${resourceItems}</div>`+
    `<div class="mobile-piece-counts">${pieceHtml}</div>`;
}
function setupResponsiveGameUi(){
  document.querySelectorAll("[data-mobile-view]").forEach(button=>{
    button.addEventListener("click",()=>{
      setMobileGameView(button.dataset.mobileView);
    });
  });

  setMobileGameView("board",false);
  updateDesktop1080Fit();

  window.addEventListener("resize",()=>{
    updateDesktop1080Fit();
    applyMobileBoardCrop();
    syncMobileTurnPanelPlacement();
    fitFishermenPlayerDetails();
  });

  window.addEventListener("orientationchange",()=>{
    setTimeout(()=>{
      const main=$("gameMain");
      const aside=main?.querySelector("aside");
      if(aside) aside.scrollTop=0;
      updateDesktop1080Fit();
      applyMobileBoardCrop();
      syncMobileTurnPanelPlacement();
    },120);
  });
}

function initTradeOptions(){
  const html=RESOURCES.map(r=>`<option value="${r}">${RESOURCE_JA[r]}</option>`).join("");
  $("tradeGive").innerHTML=html;
  $("tradeGet").innerHTML=html;
  $("tradeGet").value="brick";
}
document.querySelectorAll("[data-action]").forEach(button=>{
  button.addEventListener("click",()=>{
    setBuildMode(button.dataset.action);

    if(
      ["road","settlement","city"].includes(button.dataset.action) &&
      game?.buildMode===button.dataset.action
    ){
      setMobileGameView("board");
    }
  });
});
$("cancelModeBtn").addEventListener("click",()=>{ if(game&&isLocalTurn()){ game.buildMode=null; render(); }});
$("rollBtn").addEventListener("click",rollDice);
$("endTurnBtn").addEventListener("click",endTurn);
$("bankTradeBtn").addEventListener("click",bankTrade);
$("cpuTradeBtn").addEventListener("click",openPlayerTradeModal);
$("tradeGive").addEventListener("change",updateTradeRate);
$("fishClearBtn").addEventListener("click",()=>{ if(game){ game.selectedFishIndices=[]; renderFishPanel(); }});
document.querySelectorAll("[data-fish-action]").forEach(button=>{
  button.addEventListener("click",()=>{
    performFishAction(button.dataset.fishAction);

    if(button.dataset.fishAction==="road" && game?.freeRoads>0){
      setMobileGameView("board");
    }
  });
});
$("bootTransferBtn").addEventListener("click",transferOldBootHuman);
$("discardResetBtn").addEventListener("click",()=>{
  if(!discardSelection) return;
  RESOURCES.forEach(r=>discardSelection.selected[r]=0);
  renderDiscardChoices();
});
$("discardConfirmBtn").addEventListener("click",confirmDiscard);
$("choiceCancelBtn").addEventListener("click",()=>{
  const callback=choiceModalState?.onCancel;
  closeChoiceModal();
  if(typeof callback==="function") callback();
});
$("tradeCancelBtn").addEventListener("click",closeTradeModal);
$("tradeConfirmBtn").addEventListener("click",submitPlayerTrade);
$("resultBtn").addEventListener("click",openResultModal);
$("desktopResultBtn").addEventListener("click",openResultModal);

$("desktopPingBtn").addEventListener(
  "click",
  toggleBoardPingMode
);
$("mobilePingBtn").addEventListener(
  "click",
  toggleBoardPingMode
);

svg.addEventListener(
  "pointerdown",
  event=>{
    if(boardPingMode){
      handleBoardPingPointer(event);
    }
  },
  true
);

$("desktopLogBtn").addEventListener(
  "click",
  openDesktopLog
);

$("desktop1080FitBtn").addEventListener(
  "click",
  toggleDesktop1080Fit
);
$("desktopLogCloseBtn").addEventListener(
  "click",
  closeDesktopLog
);
$("desktopLogModal").addEventListener(
  "click",
  event=>{
    if(event.target===$("desktopLogModal")){
      closeDesktopLog();
    }
  }
);
$("resultCloseBtn").addEventListener("click",closeResultModal);
$("resultCloseTopBtn").addEventListener("click",closeResultModal);
$("resultModal").addEventListener("click",event=>{
  if(event.target===$("resultModal")){
    closeResultModal();
  }
});

initTradeOptions();
setupResponsiveGameUi();
preloadTileImages();
initCpuAnalysisUi();
initOnlineApp();
