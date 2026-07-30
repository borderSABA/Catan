
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

const svg = document.getElementById("board");
const NS = "http://www.w3.org/2000/svg";
const $ = (id) => document.getElementById(id);

let game = null;
let cpuTimer = null;
let cpuActionRunning = false;
let cpuScheduledKey = null;
let discardQueue = [];
let discardSelection = null;
let choiceModalState = null;
let tradeDraft = null;
let shownPendingTradeId = null;
const locallyResolvedTradeIds = new Set();
const shownAwardEventIds = new Set();
const awardDisplayQueue = [];
let awardDisplayActive = false;
let awardDisplayTimer = null;
let finalResultAutoTimer = null;
let finalResultWinnerKey = null;
let shownFishSwapKey = null;
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
    2200
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
  const box=$("log");
  if(!box) return;
  const lines=game?.logHistory||[];
  box.innerHTML=lines.map(msg=>`<div class="log-line">${escapeHtml(msg)}</div>`).join("");
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

function showResourceDelta(playerId,delta,reason="資源変動"){
  const entries=Object.entries(delta).filter(([,n])=>n!==0);
  if(!entries.length || !game) return;
  const p=playerById(playerId);
  const layer=$("resourcePopLayer");
  if(!layer) return;
  const pop=document.createElement("div");
  pop.className="resource-pop";
  pop.style.setProperty("--player-color",p.color);
  const detail=entries.map(([r,n])=>{
    const icon=RESOURCE_ICON[r]||"🎴";
    const sign=n>0?`+${n}`:`${n}`;
    const cls=n>0?"resource-plus":"resource-minus";
    return `<span class="${cls}">${icon}${sign}</span>`;
  }).join("　");
  pop.innerHTML=`<div class="resource-pop-title"><span>${p.name}</span><span class="resource-pop-reason">${reason}</span></div><div class="resource-pop-delta">${detail}</div>`;
  layer.prepend(pop);
  while(layer.children.length>6) layer.lastElementChild.remove();
  setTimeout(()=>pop.remove(),2900);
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
  clearTimeout(cpuTimer);
  cpuTimer=null;
  cpuActionRunning=false;
  cpuScheduledKey=null;
  shownAwardEventIds.clear();
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
  if(game.phase!=="setupSettlement" || !isLocalPlayer(p)) return;
  if(!canPlaceSettlement(p.id,vertexId,true)){ log("そこには開拓地を置けません。"); return; }
  placeSettlement(p.id,vertexId,true);
  game.setupVertex=vertexId;
  game.phase="setupRoad";
  log(`${p.name}が初期開拓地を置きました。隣接する辺に街道を置いてください。`);
  render();
}
function setupClickEdge(edgeId){
  const p=currentPlayer();
  if(game.phase!=="setupRoad" || !isLocalPlayer(p)) return;
  if(!canPlaceRoad(p.id,edgeId,game.setupVertex)){ log("初期開拓地に接する辺を選んでください。"); return; }
  game.board.edges[edgeId].road=p.id; p.roads.push(edgeId); p.pieces.road--;
  log(`${p.name}が初期街道を置きました。`);
  advanceSetup();
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
  animateDiceRoll(currentPlayer().id,()=>{});
}

function animateDiceRoll(playerId,afterResolve){
  if(game.diceRolling) return;
  game.diceRolling=true;
  const d1=$("die1"), d2=$("die2");
  d1.classList.add("rolling"); d2.classList.add("rolling");
  render();
  let ticks=0;
  const interval=setInterval(()=>{
    game.dice=[1+rand(6),1+rand(6)];
    d1.textContent=game.dice[0]; d2.textContent=game.dice[1];
    ticks++;
    if(ticks>=11){
      clearInterval(interval);
      d1.classList.remove("rolling"); d2.classList.remove("rolling");
      game.diceRolling=false;
      const finalDice=[1+rand(6),1+rand(6)];
      resolveDiceRoll(playerId,finalDice,afterResolve);
    }
  },65);
}

function resolveDiceRoll(playerId,dice,afterResolve){
  game.dice=[...dice];
  game.turnDice=[...dice];
  game.rolled=true;
  recordDiceResult(playerId,dice);
  const p=playerById(playerId);
  const sum=dice[0]+dice[1];
  log(`${p.name}が ${sum} を出しました。`);
  if(sum===7){
    queueAwardEvent("robberAppears");
    handleSeven(playerId,afterResolve);
    render();
    return;
  }
  produce(sum);
  render();
  if(typeof afterResolve==="function" && game.phase==="turn" && !game.winner){
    setTimeout(afterResolve,280);
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

function cpuDiscardHalf(player,need){
  const removed={};
  let left=need;
  while(left>0){
    const r=[...RESOURCES].sort((a,b)=>player.resources[b]-player.resources[a])[0];
    player.resources[r]--; game.bank[r]++;
    removed[r]=(removed[r]||0)-1; left--;
  }
  showResourceDelta(player.id,{unknown:-need},"7の破棄");
  log(`${player.name}は資源を${need}枚捨てました。`);
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
  const removed={};
  for(const r of RESOURCES){
    const n=discardSelection.selected[r];
    if(!n) continue;
    player.resources[r]-=n;
    game.bank[r]+=n;
    removed[r]=-n;
  }
  showResourceDelta(player.id,removed,"7の破棄");
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
    if(ONLINE_MODE && !isOnlineHost()) return;
    setTimeout(()=>{
      cpuDiscardHalf(player,need);
      game.discardQueue.shift();
      game.discardPlayerId=null;
      processDiscardQueue();
    },260);
  }else if(isLocalPlayer(player)){
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
    setTimeout(()=>cpuMoveRobber(game.robberMover),260);
  }
}

function finishRobberMove(playerId,victimId=null){
  if(victimId!==null) stealRandom(playerId,victimId);
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
    setTimeout(continuation,280);
  }else if(
    resumeCpuBuild &&
    game.current===playerId &&
    !playerById(playerId).human &&
    (!ONLINE_MODE || isOnlineHost())
  ){
    setTimeout(()=>cpuBuildPhase(playerById(playerId)),280);
  }
}

function moveRobberTo(hexId,playerId){
  if(hexId===game.robberHex) return false;
  game.robberHex=hexId;
  const victims=new Set();
  for(const vid of game.board.hexes[hexId].corners){
    const b=game.board.vertices[vid].building;
    if(b && b.player!==playerId && totalResources(playerById(b.player))>0) victims.add(b.player);
  }
  const candidates=[...victims].map(playerById);
  if(candidates.length && isLocalPlayer(playerById(playerId))){
    game.phase="chooseVictim";
    render();
    openChoiceModal({
      title:"資源を奪う相手",
      guide:"この土地に隣接するプレイヤーから、資源をランダムに1枚奪います。",
      options:playerChoiceOptions(
        candidates,
        player=>`資源カード ${totalResources(player)}枚`
      ),
      allowCancel:false,
      onSelect:victimId=>finishRobberMove(playerId,victimId),
    });
  }else{
    const victimId=candidates.length?candidates[rand(candidates.length)].id:null;
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

  const visible=isLocalPlayer(thief)||isLocalPlayer(victim);
  showResourceDelta(thiefId,visible?{[r]:1}:{unknown:1},reason);
  showResourceDelta(victimId,visible?{[r]:-1}:{unknown:-1},reason);
  log(`${thief.name}が${reason==="🐱"?"🐱で":"魚の効果で"}${victim.name}から資源を1枚奪いました。`);
}
function cpuMoveRobber(playerId){
  const options=game.board.hexes.filter(h=>h.id!==game.robberHex);
  options.sort((a,b)=>robberTargetScore(b,playerId)-robberTargetScore(a,playerId));
  moveRobberTo(options[0].id,playerId);
}
function robberTargetScore(h,playerId){
  let score=0;
  for(const vid of h.corners){
    const b=game.board.vertices[vid].building;
    if(!b) continue;
    const v=b.type==="city"?2:1;
    score += b.player===playerId ? -v*5 : v*3;
  }
  const productionWeight=h.number?PIPS[h.number]:(h.lakeNumbers||[]).reduce((s,n)=>s+(PIPS[n]||0),0)/2;
  return score+productionWeight;
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
    buyDev(p.id); checkVictory(); render(); return;
  }
  game.buildMode=mode; render();
}

function normalClickVertex(vertexId){
  const p=currentPlayer();
  if(!isLocalPlayer(p) || game.phase!=="turn" || !game.rolled) return;
  if(game.buildMode==="settlement"){
    if(!canPlaceSettlement(p.id,vertexId,false)){ log("そこには開拓地を建てられません。"); return; }
    payCost(p,COST.settlement,"開拓地建設"); placeSettlement(p.id,vertexId,false);
    p.builtThisTurn=true;
    log("あなたが開拓地を建てました。"); game.buildMode=null;
  } else if(game.buildMode==="city"){
    if(!canUpgradeCity(p.id,vertexId)){ log("自分の開拓地を選んでください。"); return; }
    placeCity(p.id,vertexId);
    p.builtThisTurn=true;
    log("あなたが都市を建てました。"); game.buildMode=null;
  }
  updateAwards(); checkVictory(); render();
}
function normalClickEdge(edgeId){
  const p=currentPlayer();
  if(!isLocalPlayer(p) || game.phase!=="turn") return;
  const free=game.freeRoads>0;
  if(game.buildMode!=="road" && !free) return;
  if(!canPlaceRoad(p.id,edgeId)){ log("そこには街道を建てられません。"); return; }
  if(!free && !game.rolled) return;
  placeRoad(p.id,edgeId,free);
  log(`あなたが街道を建てました${free?"（無料）":""}。`);
  if(free){
    game.freeRoads--;
    if(game.freeRoads===0) game.buildMode=null;
  } else {
    p.builtThisTurn=true;
    game.buildMode=null;
  }
  checkVictory(); render();
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

function cpuAcceptTrade(cpu,give,get){
  for(const resource of RESOURCES){
    if(get[resource]>cpu.resources[resource]) return false;
  }
  const receivedValue=RESOURCES.reduce(
    (sum,r)=>sum+give[r]*cpuTradeResourceValue(cpu,r),0
  );
  const paidValue=RESOURCES.reduce(
    (sum,r)=>sum+get[r]*cpuTradeResourceValue(cpu,r),0
  );
  if(receivedValue>paidValue*1.08) return true;
  if(receivedValue>=paidValue*.95) return Math.random()<.55;
  return false;
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

  const cpuWantedToAccept=cpuAcceptTrade(target,give,get);
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
  const candidates=game.players.filter(p=>p.id!==playerId&&totalResources(p)>0);
  if(!candidates.length) return null;
  const player=playerById(playerId);
  if(!isLocalPlayer(player)) return candidates.sort((a,b)=>totalResources(b)-totalResources(a))[0].id;
  return candidates;
}

function executeFishAction(action,target,payment){
  const p=currentPlayer(),cost=FISH_ACTION_COST[action];
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

function confirmFishAction(action,target=null){
  const p=currentPlayer(),cost=FISH_ACTION_COST[action];
  const payment=getHumanFishPayment(cost);
  if(!payment){
    if(game.selectedFishIndices.length){
      log(`選択中の魚は${selectedFishTotal()}匹分です。${cost}匹分以上を選んでください。`);
    }else{
      log(`${cost}匹分を支払える魚チップの組み合わせがありません。`);
    }
    return;
  }
  if(payment.total>cost){
    openConfirmModal(
      "魚の支払い確認",
      `${payment.total}匹分を使います。超過した${payment.total-cost}匹分は戻りません。`,
      ()=>executeFishAction(action,target,payment)
    );
  }else{
    executeFishAction(action,target,payment);
  }
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
    const candidates=chooseVictim(p.id);
    if(!candidates?.length){
      log("資源を持つ相手がいません。");
      return;
    }
    openChoiceModal({
      title:"魚3匹：資源を奪う",
      guide:"資源をランダムに1枚奪う相手を選択してください。",
      options:playerChoiceOptions(
        candidates,
        player=>`資源カード ${totalResources(player)}枚`
      ),
      onSelect:targetId=>confirmFishAction(action,targetId),
      allowCancel:true,
    });
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
    onSelect:targetId=>transferOldBoot(p.id,targetId),
    allowCancel:true,
  });
}
function cpuTransferBoot(player){
  if(game.oldBootHolder!==player.id) return false;
  const candidates=eligibleBootRecipients(player).sort((a,b)=>publicVP(b)-publicVP(a));
  return candidates.length?transferOldBoot(player.id,candidates[0].id):false;
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
function cpuUseFish(player){
  if(!game.fishermen) return;
  let actions=0;
  while(actions<3){
    if(game.devDeck.length && findFishPayment(player.fishTokens,7)){
      cpuSpendFish(player,7,"無料発展カード");
      if(grantFreeDevelopmentCard(player,`${player.name}の魚7匹`)) actions++;
      continue;
    }
    if(!cpuHasBuildOption(player) && findFishPayment(player.fishTokens,4)){
      const goals=[COST.city,COST.settlement,COST.road,COST.dev];
      let missing=null;
      for(const goal of goals){
        missing=RESOURCES.find(r=>(goal[r]||0)>player.resources[r]&&game.bank[r]>0);
        if(missing) break;
      }
      if(missing){
        cpuSpendFish(player,4,`${RESOURCE_JA[missing]}獲得`);
        const got=gainResource(player,missing,1);
        showResourceDelta(player.id,{[missing]:got},"魚4匹");
        actions++; continue;
      }
    }
    if(player.pieces.road>0 && findFishPayment(player.fishTokens,5)){
      const edges=Object.keys(game.board.edges).filter(e=>canPlaceRoad(player.id,e)).sort((a,b)=>roadExpansionScore(b,player.id)-roadExpansionScore(a,player.id));
      if(edges.length){ cpuSpendFish(player,5,"無料街道"); placeRoad(player.id,edges[0],true); log(`${player.name}が魚で無料街道を建てました。`); actions++; continue; }
    }
    if(robberHurtsPlayer(player)&&game.robberHex!==null&&findFishPayment(player.fishTokens,2)){
      cpuSpendFish(player,2,"🐱を盤外へ");
      game.robberHex=null;
      queueAwardEvent("fishRemoveRobber",player.id);
      log(`${player.name}が魚で🐱を盤外へ追い出しました。`);
      actions++;
      continue;
    }
    if(findFishPayment(player.fishTokens,3)&&Math.random()<.35){
      const victim=chooseVictim(player.id);
      if(victim!==null){ cpuSpendFish(player,3,"資源強奪"); stealRandom(player.id,victim,"魚3匹"); actions++; continue; }
    }
    break;
  }
}

function removeDevCard(player,card){
  const index=player.dev.findIndex(item=>item===card);
  if(index<0) return false;
  player.dev.splice(index,1);
  return true;
}

function chooseYearOfPlentyResources(player,selected=[]){
  if(selected.length>=2){
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
  resetActivePlayerState(old);
  const nextPlayer=(game.current+1)%game.playerCount;
  if(nextPlayer===0) game.turnNo++;
  game.current=nextPlayer;
  game.turnSerial++;
  game.rolled=false;
  game.dice=[0,0];
  game.turnDice=[0,0];
  game.phase="turn";
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
  },450);
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
    log(`${p.name}が初期開拓地を置きました。`);
    render();
    scheduleCpuIfNeeded();
    return;
  }
  if(game.phase==="setupRoad"){
    const options=game.board.vertices[game.setupVertex].edges.filter(e=>canPlaceRoad(p.id,e,game.setupVertex));
    options.sort((a,b)=>futureVertexScore(otherEnd(a,game.setupVertex))-futureVertexScore(otherEnd(b,game.setupVertex)));
    const e=options[options.length-1] || options[0];
    game.board.edges[e].road=p.id; p.roads.push(e); p.pieces.road--;
    log(`${p.name}が初期街道を置きました。`);
    advanceSetup(); return;
  }
  if(game.phase==="moveRobber"){
    cpuMoveRobber(p.id);
    cpuTimer=setTimeout(()=>cpuBuildPhase(p),300);
    return;
  }
  if(game.phase!=="turn"){
    cpuActionRunning=false;
    return;
  }

  cpuActionRunning=true;

  if(game.fishermen){
    cpuTransferBoot(p);
    if(game.winner) return;
  }
  animateDiceRoll(p.id,()=>cpuBuildPhase(p));
}

function cpuBuildPhase(p){
  if(game.winner || game.current!==p.id) return;

  cpuUseFish(p);
  checkVictory();
  if(game.winner){
    cpuActionRunning=false;
    render();
    return;
  }

  // 発展カードは購入ターンを含め、1ターンに何枚でも使用可能
  const vpCount=usableDevCount(p,"vp");
  const neededForWin=Math.max(0,victoryTarget(p)-totalVP(p));
  if(vpCount>0){
    if(neededForWin>0 && neededForWin<=vpCount){
      for(let i=0;i<neededForWin && !game.winner;i++) cpuPlayVictoryPoint(p);
    } else if(Math.random()<.22){
      cpuPlayVictoryPoint(p);
    }
    if(game.winner){
      cpuActionRunning=false;
      render();
      return;
    }
  }

  // 騎士使用後は再びこの処理へ戻るため、続けて複数枚使用することもある
  if(usableDevCount(p,"knight")>0 && Math.random()<.28){
    cpuPlayKnight(p);
    return;
  }

  // 建設前に、必要なら銀行・港交易を数回試す
  for(let i=0;i<4 && !p.builtThisTurn;i++){
    if(cpuHasBuildOption(p)) break;
    if(!cpuTryBankTrade(p)) break;
  }

  // 街道・開拓地・都市・発展カード購入のうち、各ターン1回だけ
  if(!p.builtThisTurn && p.pieces.city>0 && hasCost(p,COST.city)){
    const targets=p.settlements.slice().sort((a,b)=>vertexProductionScore(b)-vertexProductionScore(a));
    if(targets.length){
      placeCity(p.id,targets[0]);
      p.builtThisTurn=true;
      log(`${p.name}が都市を建てました。`);
    }
  }
  if(!p.builtThisTurn && p.pieces.settlement>0 && hasCost(p,COST.settlement)){
    const targets=Object.keys(game.board.vertices).filter(v=>canPlaceSettlement(p.id,v,false));
    targets.sort((a,b)=>vertexProductionScore(b)-vertexProductionScore(a));
    if(targets.length){
      payCost(p,COST.settlement,"開拓地建設");
      placeSettlement(p.id,targets[0],false);
      p.builtThisTurn=true;
      log(`${p.name}が開拓地を建てました。`);
    }
  }
  if(!p.builtThisTurn && p.pieces.road>0 && hasCost(p,COST.road)){
    const targets=Object.keys(game.board.edges).filter(e=>canPlaceRoad(p.id,e));
    targets.sort((a,b)=>roadExpansionScore(b,p.id)-roadExpansionScore(a,p.id));
    if(targets.length && (p.roads.length<4 || Math.random()<.7)){
      placeRoad(p.id,targets[0],false);
      p.builtThisTurn=true;
      log(`${p.name}が街道を建てました。`);
    }
  }
  if(!p.builtThisTurn && game.devDeck.length && hasCost(p,COST.dev) && Math.random()<.55){
    buyDev(p.id);
  }

  updateAwards();
  checkVictory();
  render();
  if(!game.winner){
    clearTimeout(cpuTimer);
    cpuTimer=setTimeout(()=>{
      cpuTimer=null;
      if(!game || game.winner || game.current!==p.id || p.human){
        cpuActionRunning=false;
        return;
      }
      finishActivePhase();
    },450);
  }else{
    cpuActionRunning=false;
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
  const goals=[COST.city,COST.settlement,COST.road,COST.dev];
  let target=null, missing=null;
  for(const g of goals){
    const miss=RESOURCES.filter(r=>(g[r]||0)>p.resources[r]);
    if(miss.length===1){ target=g; missing=miss[0]; break; }
  }
  if(!target || game.bank[missing]<1) return false;
  const give=RESOURCES
    .filter(r=>r!==missing && p.resources[r]>=getTradeRate(p,r))
    .sort((a,b)=>(p.resources[b]-(target[b]||0))-(p.resources[a]-(target[a]||0)))[0];
  if(!give) return false;
  const rate=getTradeRate(p,give);
  p.resources[give]-=rate; game.bank[give]+=rate; p.resources[missing]++; game.bank[missing]--;
  showResourceDelta(p.id,{[give]:-rate,[missing]:1},"銀行・港交易");
  log(`${p.name}が銀行・港と交易しました。`);
  return true;
}

function cpuPlayVictoryPoint(p){
  const idx=p.dev.findIndex(c=>c==="vp");
  if(idx<0 || usableDevCount(p,"vp")<=0) return;
  p.dev.splice(idx,1);
  queueAwardEvent("devVictoryPoint",p.id);
  p.revealedVP++;
  log(`${p.name}が勝利ポイントカードを公開しました。`);
  checkVictory();
}

function cpuPlayKnight(p){
  const idx=p.dev.indexOf("knight");
  if(idx<0) return;
  p.dev.splice(idx,1);
  queueAwardEvent("devKnight",p.id);
  p.knightsPlayed++;
  updateAwards();
  log(`${p.name}が騎士を使いました。`);
  game.phase="moveRobber"; game.robberMover=p.id;
  cpuMoveRobber(p.id);
  render();
  clearTimeout(cpuTimer);
  cpuTimer=setTimeout(()=>{
    cpuTimer=null;
    if(!game || game.winner || game.current!==p.id || p.human){
      cpuActionRunning=false;
      return;
    }
    cpuBuildPhase(p);
  },300);
}
function usableDevCount(p,card){
  return p.dev.filter(c=>c===card).length;
}
function otherEnd(edgeId,vertexId){
  const e=game.board.edges[edgeId]; return e.a===vertexId?e.b:e.a;
}
function futureVertexScore(v){ return vertexProductionScore(v); }
function bestSetupVertex(playerId){
  const candidates=Object.keys(game.board.vertices).filter(v=>canPlaceSettlement(playerId,v,true));
  candidates.sort((a,b)=>setupVertexScore(b,playerId)-setupVertexScore(a,playerId));
  return candidates[0];
}
function setupVertexScore(v,playerId){
  const base=vertexProductionScore(v);
  const resources=new Set(game.board.vertices[v].hexes.map(h=>game.board.hexes[h].resource).filter(r=>RESOURCES.includes(r)));
  const fishing=game.fishermen&&isFishingVertex(v)?3:0;
  return base+resources.size*2+fishing+Math.random()*2;
}
function vertexProductionScore(v){
  return game.board.vertices[v].hexes.reduce((s,h)=>{
    const x=game.board.hexes[h];
    if(x.number) return s+(PIPS[x.number]||0);
    if(x.resource==="lake") return s+x.lakeNumbers.reduce((n,v)=>n+(PIPS[v]||0),0)*.45;
    return s;
  },0);
}
function roadExpansionScore(edgeId,playerId){
  const e=game.board.edges[edgeId];
  return vertexProductionScore(e.a)+vertexProductionScore(e.b)+Math.random()*2;
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
  }
}

function render(){
  if(!game) return;
  enforceResourceIntegrity();
  renderBoard();
  renderSide();
  renderLog();
  collectAwardAnnouncements();
  scheduleFinalResultIfNeeded();
  onlineAfterRender();
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
      poly.addEventListener("click",()=>{ if(h.id!==game.robberHex) moveRobberTo(h.id,currentPlayer().id); });
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
        svg.appendChild(createSvg("circle",{cx:h.x+ox,cy:h.y+oy,r:game.board.large?14:16,class:"lake-number"}));
        const t=createSvg("text",{x:h.x+ox,y:h.y+oy+1,class:"lake-number-text",style:`font-size:${game.board.large?13:15}px`});
        t.textContent=num; svg.appendChild(t);
      });
      const fish=createSvg("text",{x:h.x,y:h.y+(nums.length===4?0:28),class:"fishing-ground-fish",style:`font-size:${game.board.large?18:22}px`});
      fish.textContent="🐟"; svg.appendChild(fish);
    }else if(h.number){
      svg.appendChild(createSvg("circle",{cx:h.x,cy:h.y,r:tokenRadius,class:"number-token"}));
      const t=createSvg("text",{x:h.x,y:h.y-3,class:`number-text ${[6,8].includes(h.number)?"hot-number":""}`,style:`font-size:${numberSize}px`});
      t.textContent=h.number; svg.appendChild(t);
      const p=createSvg("text",{x:h.x,y:h.y+(game.board.large?14:17),class:"pip-text"});
      p.textContent="•".repeat(PIPS[h.number]); svg.appendChild(p);
    }
    if(game.robberHex===h.id){
      const cat=createSvg("text",{x:h.x,y:h.y+7,class:"robber-cat",style:`font-size:${game.board.large?34:42}px`});
      cat.textContent="🐱";
      svg.appendChild(cat);
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
    const hit=createSvg("circle",{cx:v.x,cy:v.y,r:game.board.large?11:14,class:"vertex-click"});
    hit.addEventListener("click",()=>{
      if(game.phase==="setupSettlement") setupClickVertex(v.id);
      else normalClickVertex(v.id);
    });
    svg.appendChild(hit);
  }

  boardBuildFinished=true;
  applyMobileBoardCrop();
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

  $("players").innerHTML=game.players.map(player=>{
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
      `街道${player.longestRoad}`,
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
  xEnd:19,
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

function applyMobileBoardCrop(){
  const smartphone=
    typeof isSmartphoneGameViewport==="function"
      ?isSmartphoneGameViewport()
      :window.matchMedia("(max-width: 720px)").matches;

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

    if(smartphone){
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

  if(scrollToTop && window.matchMedia("(max-width: 720px)").matches){
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

  window.addEventListener("resize",()=>{
    applyMobileBoardCrop();
    syncMobileTurnPanelPlacement();
  });

  window.addEventListener("orientationchange",()=>{
    setTimeout(()=>{
      const main=$("gameMain");
      const aside=main?.querySelector("aside");
      if(aside) aside.scrollTop=0;
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
initOnlineApp();
