"use strict";

const ONLINE_MODE = true;
const ROOM_IDS = ["room1","room2","room3","room4"];
const ONLINE_STORAGE = {
  clientId:"catan-online-client-id",
  name:"catan-online-player-name",
  roomId:"catan-online-room-id",
};
const SERVER_ORIGIN = String(window.CATAN_SERVER_URL||"").replace(/\/+$/,"");

let onlineSocket = null;
let onlineRoomState = null;
let onlineRoomId = null;
let applyingRemoteState = false;
let suppressOnlineSync = false;
let onlineSyncTimer = null;
let roomRefreshTimer = null;
let reconnectTimer = null;
let reconnectAttempts = 0;

function makeClientId(){
  return crypto.randomUUID?.() || `${Date.now()}-${Math.random().toString(36).slice(2)}`;
}
const ONLINE_CLIENT_ID = localStorage.getItem(ONLINE_STORAGE.clientId) || makeClientId();
localStorage.setItem(ONLINE_STORAGE.clientId,ONLINE_CLIENT_ID);

function localPlayerId(){
  if(!game) return -1;
  if(!ONLINE_MODE) return 0;
  const player=game.players.find(p=>p.clientId===ONLINE_CLIENT_ID);
  return player?.id??-1;
}
function localPlayer(){
  return game?.players?.find(p=>p.clientId===ONLINE_CLIENT_ID) || game?.players?.[0] || null;
}
function isLocalPlayer(player){
  if(!player) return false;
  return ONLINE_MODE ? player.clientId===ONLINE_CLIENT_ID : player.id===0;
}
function isLocalTurn(){
  return !!game && isLocalPlayer(currentPlayer());
}
function isOnlineHost(){
  return onlineRoomState?.hostId===ONLINE_CLIENT_ID;
}
function scheduleCpuIfNeeded(){
  if(!game || game.winner || !currentPlayer()){
    clearTimeout(cpuTimer);
    cpuTimer=null;
    cpuScheduledKey=null;
    return;
  }

  if(currentPlayer().human){
    clearTimeout(cpuTimer);
    cpuTimer=null;
    cpuScheduledKey=null;
    cpuActionRunning=false;
    return;
  }

  if(game.diceRolling || cpuActionRunning) return;
  if(!ONLINE_MODE || isOnlineHost()) scheduleCpu();
}

function wsOrigin(){
  return SERVER_ORIGIN.replace(/^http:/,"ws:").replace(/^https:/,"wss:");
}
function onlineSend(payload){
  if(onlineSocket?.readyState!==WebSocket.OPEN) return false;
  onlineSocket.send(JSON.stringify(payload));
  return true;
}
function cloneGameForNetwork(){
  return JSON.parse(JSON.stringify(game,(key,value)=>{
    if(typeof value==="function") return undefined;
    if(key==="pendingAfterRobber") return null;
    return value;
  }));
}
function onlineAfterRender(){
  if(!ONLINE_MODE || !game || applyingRemoteState || suppressOnlineSync) return;
  handleOnlinePendingUI();
  if(!onlineRoomState || onlineRoomState.phase!=="playing") return;
  clearTimeout(onlineSyncTimer);
  onlineSyncTimer=setTimeout(()=>{
    if(applyingRemoteState || suppressOnlineSync || !game) return;
    onlineSend({type:"game_state",game:cloneGameForNetwork()});
  },35);
}

function setSocketState(text,stateClass=""){
  const el=document.getElementById("onlineSocketState");
  if(!el) return;
  el.textContent=text;
  el.className=`socket-state ${stateClass}`;
}
function showOnlineMessage(text,error=false){
  const el=document.getElementById("onlineConnectionMessage");
  if(!el) return;
  el.textContent=text;
  el.classList.toggle("error",error);
}

async function fetchRoomSummaries(){
  if(!SERVER_ORIGIN || SERVER_ORIGIN.includes("YOUR-")){
    showOnlineMessage("config.jsのCloudflare Worker URLを設定してください。",true);
    return;
  }
  try{
    const response=await fetch(`${SERVER_ORIGIN}/rooms`,{cache:"no-store"});
    if(!response.ok) throw new Error(`HTTP ${response.status}`);
    const data=await response.json();
    renderRoomCards(data.rooms||[]);
    showOnlineMessage("入室する部屋を選択してください。現在の版：v1.10");
  }catch(error){
    showOnlineMessage(`部屋情報を取得できません：${error.message}`,true);
  }
}

function renderRoomCards(rooms){
  const byId=new Map(rooms.map(room=>[room.roomId,room]));
  $("roomCards").innerHTML=ROOM_IDS.map((roomId,index)=>{
    const room=byId.get(roomId)||{phase:"lobby",connected:0,members:0,settings:{playerCount:4,fishermen:true,cpuFill:false}};
    const playing=room.phase==="playing";
    const full=room.connected>=6;
    const stateText=playing?"対戦中":"ロビー";
    return `<button class="room-card ${playing?"playing":""} ${full?"full":""}" data-room-id="${roomId}" ${playing||full?"disabled":""}>
      <span class="room-card-title">部屋 ${index+1}</span>
      <span class="room-card-state">${stateText}</span>
      <span class="room-card-count">接続 ${room.connected}/6人</span>
    </button>`;
  }).join("");
  document.querySelectorAll("[data-room-id]").forEach(button=>{
    button.addEventListener("click",()=>joinOnlineRoom(button.dataset.roomId));
  });
}

function currentOnlineName(){
  return ($("onlinePlayerName").value||"").trim().slice(0,12);
}
function joinOnlineRoom(roomId){
  const name=currentOnlineName();
  if(!name){
    showOnlineMessage("名前を入力してください。",true);
    $("onlinePlayerName").focus();
    return;
  }
  localStorage.setItem(ONLINE_STORAGE.name,name);
  onlineRoomId=roomId;
  localStorage.setItem(ONLINE_STORAGE.roomId,roomId);
  clearTimeout(reconnectTimer);
  if(onlineSocket) onlineSocket.close();
  const url=new URL(`${wsOrigin()}/ws`);
  url.searchParams.set("room",roomId);
  url.searchParams.set("clientId",ONLINE_CLIENT_ID);
  url.searchParams.set("name",name);
  showOnlineMessage("部屋へ接続しています……");
  onlineSocket=new WebSocket(url);
  setSocketState("接続中","");

  onlineSocket.addEventListener("open",()=>{
    reconnectAttempts=0;
    setSocketState("接続中","connected");
  });
  onlineSocket.addEventListener("message",event=>{
    let message;
    try{ message=JSON.parse(event.data); }catch{ return; }
    if(message.type==="error"){
      showOnlineMessage(message.message||"接続エラー",true);
      return;
    }
    if(message.type==="room_state"){
      receiveRoomState(message.state);
    }
  });
  onlineSocket.addEventListener("close",()=>{
    setSocketState("切断","disconnected");
    if(onlineRoomId){
      reconnectAttempts++;
      const wait=Math.min(8000,800*reconnectAttempts);
      reconnectTimer=setTimeout(()=>joinOnlineRoom(onlineRoomId),wait);
    }
  });
  onlineSocket.addEventListener("error",()=>{
    setSocketState("接続エラー","disconnected");
  });
}

const APP_VERSION="v1.10";

function setScreenElement(element,visible,displayValue){
  if(!element) return;
  element.hidden=!visible;
  element.classList.toggle("hidden",!visible);
  if(visible){
    element.style.setProperty("display",displayValue,"important");
  }else{
    element.style.setProperty("display","none","important");
  }
}

function showLobbyScreen(){
  document.body.classList.add("online-lobby-mode");
  document.body.classList.remove("online-game-mode");
  setScreenElement($("onlineLobby"),true,"grid");
  setScreenElement($("gameHeader"),false,"flex");
  setScreenElement($("gameMain"),false,"grid");
  document.title=`カタン オンライン ${APP_VERSION}（ロビー）`;
  window.scrollTo(0,0);
}

function showGameScreen(){
  document.body.classList.remove("online-lobby-mode");
  document.body.classList.add("online-game-mode");
  setScreenElement($("onlineLobby"),false,"grid");
  setScreenElement($("gameHeader"),true,"flex");
  setScreenElement($("gameMain"),true,"grid");
  document.title=`カタン オンライン ${APP_VERSION}（対戦中）`;
  window.scrollTo(0,0);
}

function receiveRoomState(state){
  onlineRoomState=state;
  onlineRoomId=state.roomId;
  renderOnlineLobby();
  if(state.phase==="playing" && state.game){
    applyingRemoteState=true;
    game=state.game;
    if(!Array.isArray(game.logHistory)) game.logHistory=[];
    if(!Array.isArray(game.discardQueue)) game.discardQueue=[];
    if(!Array.isArray(game.pendingFishDraws)) game.pendingFishDraws=[];
    showGameScreen();
    $("currentRoomLabel").textContent=`部屋 ${ROOM_IDS.indexOf(state.roomId)+1}`;
    const cpuCount=game.players.filter(player=>!player.human).length;
    $("onlineGameSubtitle").textContent=`${game.playerCount}人用${cpuCount?`・CPU${cpuCount}人`:""}${game.fishermen?"・漁師拡張":""}`;
    render();
    applyingRemoteState=false;

    if(currentPlayer()?.human){
      clearTimeout(cpuTimer);
      cpuTimer=null;
      cpuScheduledKey=null;
      cpuActionRunning=false;
    }

    handleOnlinePendingUI();
    scheduleCpuIfNeeded();
  }else{
    game=null;
    closeChoiceModal();
    closeTradeModal();
    hideDiscardModal();
    showLobbyScreen();
  }
}

function renderOnlineLobby(){
  if(!onlineRoomState){
    $("roomSelectView").classList.remove("hidden");
    $("joinedRoomView").classList.add("hidden");
    return;
  }
  $("roomSelectView").classList.add("hidden");
  $("joinedRoomView").classList.remove("hidden");
  const roomNumber=ROOM_IDS.indexOf(onlineRoomState.roomId)+1;
  $("joinedRoomTitle").textContent=`部屋 ${roomNumber}`;
  $("joinedRoomStatus").textContent=onlineRoomState.phase==="playing"?"対戦中":"参加者が揃うのを待っています。";

  const connectedMembers=onlineRoomState.members.filter(member=>member.connected);
  const connected=connectedMembers.length;
  const needed=onlineRoomState.settings.playerCount;
  const cpuFill=!!onlineRoomState.settings.cpuFill;
  const cpuCount=cpuFill?Math.max(0,needed-connected):0;

  const memberHtml=onlineRoomState.members.map((member,index)=>`
    <div class="online-member ${member.connected?"":"disconnected"}">
      <span class="player-dot" style="background:${PLAYER_COLORS[index]||"#64748b"}"></span>
      <span>${escapeHtml(member.name)}${member.clientId===ONLINE_CLIENT_ID?"（あなた）":""}<br><small>${member.connected?"接続中":"切断中"}</small></span>
      ${member.clientId===onlineRoomState.hostId?'<span class="online-member-host">ホスト</span>':""}
    </div>
  `).join("");

  const cpuHtml=Array.from({length:cpuCount},(_,index)=>{
    const seatIndex=connected+index;
    return `<div class="online-member cpu-preview">
      <span class="player-dot" style="background:${PLAYER_COLORS[seatIndex]||"#64748b"}"></span>
      <span>CPU ${index+1}<br><small>ゲーム開始時に追加</small></span>
      <span class="online-member-cpu">CPU</span>
    </div>`;
  }).join("");
  $("onlineMembers").innerHTML=memberHtml+cpuHtml;

  const host=isOnlineHost();
  $("playerCount").value=String(onlineRoomState.settings.playerCount);
  $("fishermenEnabled").checked=!!onlineRoomState.settings.fishermen;
  $("cpuFillEnabled").checked=cpuFill;
  $("playerCount").disabled=!host;
  $("fishermenEnabled").disabled=!host;
  $("cpuFillEnabled").disabled=!host;
  $("resetLobbyRoomBtn").classList.toggle("hidden",!host);

  const ready=cpuFill
    ? connected>=1 && connected<=needed
    : connected===needed;

  if(connected>needed){
    $("startRequirement").textContent=`設定は${needed}人ですが、人間が${connected}人います。参加人数を増やしてください。`;
  }else if(cpuFill){
    $("startRequirement").textContent=ready
      ? `人間${connected}人＋CPU${cpuCount}人で開始できます。`
      : `最低1人の人間プレイヤーが必要です。`;
  }else{
    $("startRequirement").textContent=connected===needed
      ? `${connected}人揃っています。開始できます。`
      : `設定は${needed}人です。現在${connected}人接続中です。`;
  }

  $("startOnlineGameBtn").disabled=!host || !ready || onlineRoomState.phase!=="lobby";
  $("startOnlineGameBtn").textContent=host
    ? (cpuFill&&cpuCount>0?"CPUを含めてゲーム開始":"ゲーム開始")
    : "ホストの開始待ち";
}

function sendSettings(){
  if(!isOnlineHost()) return;
  onlineSend({
    type:"set_settings",
    settings:{
      playerCount:Number($("playerCount").value),
      fishermen:$("fishermenEnabled").checked,
      cpuFill:$("cpuFillEnabled").checked,
    },
  });
}

function startOnlineGame(){
  if(!isOnlineHost() || !onlineRoomState) return;
  const members=onlineRoomState.members.filter(member=>member.connected);
  const playerCount=onlineRoomState.settings.playerCount;
  const cpuFill=!!onlineRoomState.settings.cpuFill;
  const valid=cpuFill
    ? members.length>=1 && members.length<=playerCount
    : members.length===playerCount;
  if(!valid) return;

  suppressOnlineSync=true;
  $("playerCount").value=String(playerCount);
  $("fishermenEnabled").checked=!!onlineRoomState.settings.fishermen;
  newGame();

  const cpuNames=["CPUアオ","CPUキイロ","CPUムラサキ","CPUミドリ","CPUチャ"];
  game.players.forEach((player,index)=>{
    const member=members[index];
    if(member){
      player.human=true;
      player.name=member.name;
      player.clientId=member.clientId;
    }else{
      player.human=false;
      player.clientId=null;
      player.name=cpuNames[(index-members.length)%cpuNames.length]||`CPU ${index-members.length+1}`;
    }
  });

  game.online=true;
  game.roomId=onlineRoomState.roomId;
  game.pendingTrade=null;
  game.discardQueue=[];
  game.discardPlayerId=null;
  game.logHistory=[];

  const cpuCount=game.players.filter(player=>!player.human).length;
  log(`人間${members.length}人＋CPU${cpuCount}人で対戦を開始しました。`);
  if(game.fishermen) log("漁師拡張を使用します。");
  suppressOnlineSync=false;
  onlineSend({type:"start_game",game:cloneGameForNetwork()});
}

function leaveOnlineRoom(){
  onlineRoomId=null;
  localStorage.removeItem(ONLINE_STORAGE.roomId);
  clearTimeout(reconnectTimer);
  if(onlineSocket?.readyState===WebSocket.OPEN) onlineSend({type:"leave"});
  onlineSocket?.close();
  onlineSocket=null;
  onlineRoomState=null;
  game=null;
  $("joinedRoomView").classList.add("hidden");
  $("roomSelectView").classList.remove("hidden");
  $("onlineLobby").classList.remove("hidden");
  $("gameHeader").classList.add("hidden");
  $("gameMain").classList.add("hidden");
  setSocketState("未接続","disconnected");
  fetchRoomSummaries();
}

function resetOnlineRoom(){
  if(!isOnlineHost()) return;
  onlineSend({type:"reset_room"});
}

function initOnlineApp(){
  showLobbyScreen();
  const savedName=localStorage.getItem(ONLINE_STORAGE.name)||"";
  $("onlinePlayerName").value=savedName;
  $("refreshRoomsBtn").addEventListener("click",fetchRoomSummaries);
  $("leaveRoomLobbyBtn").addEventListener("click",leaveOnlineRoom);
  $("leaveRoomGameBtn").addEventListener("click",leaveOnlineRoom);
  $("returnLobbyBtn").addEventListener("click",resetOnlineRoom);
  $("resetLobbyRoomBtn").addEventListener("click",resetOnlineRoom);
  $("startOnlineGameBtn").addEventListener("click",startOnlineGame);
  $("playerCount").addEventListener("change",sendSettings);
  $("fishermenEnabled").addEventListener("change",sendSettings);
  $("cpuFillEnabled").addEventListener("change",sendSettings);
  $("onlinePlayerName").addEventListener("change",()=>{
    const name=currentOnlineName();
    if(name) localStorage.setItem(ONLINE_STORAGE.name,name);
  });

  fetchRoomSummaries();
  roomRefreshTimer=setInterval(()=>{
    if(!onlineRoomId) fetchRoomSummaries();
  },5000);

  const requestedRoom=new URLSearchParams(location.search).get("room");
  const savedRoom=localStorage.getItem(ONLINE_STORAGE.roomId);
  const roomToJoin=ROOM_IDS.includes(requestedRoom)?requestedRoom:savedRoom;
  if(ROOM_IDS.includes(roomToJoin) && savedName){
    joinOnlineRoom(roomToJoin);
  }
}
