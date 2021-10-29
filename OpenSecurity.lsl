/*
OpenSecurity

Copyright © 2021 BinaryArchitect

This work is licensed under the Creative Commons Attribution-ShareAlike 4.0 International License. To view a copy of this license, visit http://creativecommons.org/licenses/by-sa/4.0/ or send a letter to Creative Commons, PO Box 1866, Mountain View, CA 94042, USA.

-----------------------------------------------------------------------------------------------------------------

You are free to:

    Share — copy and redistribute the material in any medium or format
    Adapt — remix, transform, and build upon the material
    for any purpose, even commercially.

This license is acceptable for Free Cultural Works.

    The licensor cannot revoke these freedoms as long as you follow the license terms.

-----------------------------------------------------------------------------------------------------------------

Under the following terms:

    Attribution — You must give appropriate credit, provide a link to the license, and indicate if changes were made. You may do so in any reasonable manner, but not in any way that suggests the licensor endorses you or your use.

    ShareAlike — If you remix, transform, or build upon the material, you must distribute your contributions under the same license as the original.

    No additional restrictions — You may not apply legal terms or technological measures that legally restrict others from doing anything the license permits.

-----------------------------------------------------------------------------------------------------------------

Notices:

    You do not have to comply with the license for elements of the material in the public domain or where your use is permitted by an applicable exception or limitation.
    No warranties are given. The license may not give you all of the permissions necessary for your intended use. For example, other rights such as publicity, privacy, or moral rights may limit how you use the material.
*/

// Security that doesn't have to come at the expense of privacy or transparency.

// Notecard runtime variables
string ncName;
key ncReader;
integer ncLine;
integer ncBusy;
list ncQueue;

// Security configurables
list configWhitelist = [];
float configTimeBan = -1;
string configVerbose = "owner";
float configRange = -1;
integer configUseEstate = FALSE;
integer configEjectWithTP = FALSE;
integer configEjectOnGroup = FALSE;
integer configEjectOnFlying = FALSE;
integer configEjectOnAfk = FALSE;
integer configShowHoverText = TRUE;
integer configMinAge = -1;
integer configEjectOnNoPayment = FALSE;
integer configEjectOnUnusedPayment = FALSE;
float configMaxScriptMemory = -1;
float configMaxScriptTime = -1;
integer configMaxScriptCount = -1;
float configMaxRenderWeight = -1;
float configMaxAvatarHeight = -1;
integer configMaxAttachmentInventory = -1;
integer configEjectDelay = -1;
string configEjectDelayMessage;
integer configEjectDelayAllowedDwell = -1;
list configRestrictZones;
integer configDryRun = FALSE;

// Security runtime variables
integer securityReady;
key securitySuperAdmin;
list securityPresence;
list securityDataChecks; // [requestId, agentId, type]
integer lastSecurityPresenceCleanup;
integer lastSecuritySweep;
integer securityEstateFailures;
list securityEjectQueue; // [id, reason, mask, unixTime]

// Display state
string lastDisplay;

// Modified from http://wiki.secondlife.com/wiki/Under_Age_Boot
integer date2days(string data){
    list daysByMonth = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334];
    list parsedDate;
    integer year;
    integer days;
    
    parsedDate = llParseString2List(data, ["-", "T"], []);
    year = llList2Integer(parsedDate, 0);
    days = (year - 2000) * 365;
 
    days += llList2Integer(daysByMonth, (llList2Integer(parsedDate, 1) - 1));
    days += llFloor((year-2000) / 4);
    days += llList2Integer(parsedDate, 2);
 
    return days;
}

string floatToString(float num, integer precision){
    if (precision >= 6) return (string)num;
    else return llGetSubString((string)num,0,-6 + precision - 1);
}

default{
    state_entry(){
        // assign first owner
        securitySuperAdmin = llList2Key(llGetObjectDetails(llGetKey(), [OBJECT_REZZER_KEY]), 0);
        
        // reset display
        llMessageLinked(LINK_THIS, 0, 
            llList2Json(JSON_ARRAY, ["renderText", TRUE]),
            "");
        
        // request settings loading
        llMessageLinked(LINK_THIS, 0, 
            llList2Json(JSON_ARRAY, ["loadSettings", "config", "whitelist"]),
            "");
    }
    
    changed(integer change){
        if(change & CHANGED_INVENTORY || change & CHANGED_OWNER)
            llResetScript();
    }
    
    timer(){
        if (!securityReady) return;
        
        if (llGetUnixTime() - lastSecuritySweep > 5){
            lastSecuritySweep = llGetUnixTime();
            
            vector pos = llGetPos();
            list avs = llGetAgentList(4, []);
            vector avPos;
            vector avSize;
            key id;
            integer observe;
            integer eject;
            string reason;
            integer info;
            list details;
            
            integer i;
            integer n;
            
            vector zonePos;
            vector zoneSize;
            rotation zoneRot;
            
            // Geometric vars
            vector gBXx_eB;
            vector gBXx_rA;
            integer gBXx;
            
            
            integer pendingEjection;
            integer pendingDataChecks;
            integer needsObjectDetails = llListStatistics(LIST_STAT_MAX, [
                    configMaxScriptMemory, 
                    configMaxScriptTime,
                    configMaxScriptCount, 
                    configMaxRenderWeight,
                    configMaxAttachmentInventory
                ]) != -1;
            
            while(llGetListLength(avs) && (llOverMyLand(llGetKey()) || configUseEstate || configDryRun)){
                id = llList2Key(avs, 0);
                avs = llDeleteSubList(avs, 0, 0);
                if(
                    id != securitySuperAdmin &&                 // always ignore owner
                    (llOverMyLand(id) || configUseEstate || configDryRun) &&    // have eject capabilities
                    !~llListFindList(configWhitelist, [id])     // not on the whitelist
                    ){
                    pendingDataChecks = llListFindList(securityDataChecks, [id]);
                    pendingEjection = llListFindList(securityEjectQueue, [id]);
                    eject = FALSE;
                    reason = "";
                    observe = TRUE;
                    info = llGetAgentInfo(id);
                    if(llGetListLength(configRestrictZones)){
                        observe = FALSE;
                        avPos = llList2Vector(llGetObjectDetails(id, [OBJECT_POS]), 0);
                        for(i=0,n=llGetListLength(configRestrictZones); i<n && !observe; i+=3){
                            zonePos = llList2Vector(configRestrictZones, i);
                            zoneSize = llList2Vector(configRestrictZones, i+1);
                            zoneRot = llList2Rot(configRestrictZones, i+2);
                            
                            // http://wiki.secondlife.com/wiki/Geometric#Box_and_Point.2C_Intersection_Boolean
                            // Copyright 2001, softSurfer (www.softsurfer.com); 2008, LSL-port by Nexii Malthus
                            // This code may be freely used and modified for any purpose
                            // providing that this copyright notice is included with it.
                            // SoftSurfer makes no warranty for this code, and cannot be held
                            // liable for any real or imagined damage resulting from its use.
                            // Users of this code must verify correctness for their application.
                            // integer gBXx(vector A, vector Bo, vector Bs, rotation Br)
                            gBXx_eB = 0.5*zoneSize; 
                            gBXx_rA = (avPos-zonePos)/zoneRot;
                            gBXx = (gBXx_rA.x<gBXx_eB.x && gBXx_rA.x>-gBXx_eB.x && gBXx_rA.y<gBXx_eB.y && gBXx_rA.y>-gBXx_eB.y && gBXx_rA.z<gBXx_eB.z && gBXx_rA.z>-gBXx_eB.z);
                            
                            if(gBXx)
                                observe = TRUE;
                        }
                    }
                    else if(configRange > -1){
                        avPos = llList2Vector(llGetObjectDetails(id, [OBJECT_POS]), 0);
                        if(llVecDist(pos, avPos) > configRange)
                            observe = FALSE;
                    }
                    
                    
                    if (observe){
                        if(!~llListFindList(securityPresence, [id]) && !~pendingEjection){
                            securityPresence += id;
                            // some things we only need to check once
                            if (~configMinAge) 
                                securityDataChecks += [llRequestAgentData(id,DATA_BORN), id, "age"];
                            if (configEjectOnNoPayment || configEjectOnUnusedPayment)
                                securityDataChecks += [llRequestAgentData(id,DATA_PAYINFO), id, "pay"];
                            // any external callouts go here
                        }
                        else {
                            // check these line items every scan cycle
                            if (configEjectOnFlying && info & AGENT_FLYING){
                                reason = "flying";
                                eject = TRUE;
                            }
                            else if (configEjectOnAfk && info & AGENT_AWAY){
                                reason = "afk";
                                eject = TRUE;
                            }
                            else if (configEjectOnGroup && !llSameGroup(id)){
                                reason = "group";
                                eject = TRUE;
                            }
                            else if (configMaxAvatarHeight != -1 && avSize.z > configMaxAvatarHeight){
                                reason = (string)["height (",floatToString(avSize.z,2),"/",floatToString(configMaxAvatarHeight,2),"m)"];
                                eject = TRUE;
                            }
                            else if (needsObjectDetails){ 
                                details = llGetObjectDetails(id, [
                                    OBJECT_SCRIPT_MEMORY,
                                    OBJECT_SCRIPT_TIME,
                                    OBJECT_TOTAL_SCRIPT_COUNT, 
                                    OBJECT_RENDER_WEIGHT,
                                    OBJECT_TOTAL_INVENTORY_COUNT
                                    ]);
                                if (configMaxScriptMemory != -1 && llList2Float(details, 0) / 1024.0 > configMaxScriptMemory) {
                                    reason = (string)["script memory (",
                                        floatToString(llList2Float(details, 0) / 1024.0, 2),"/",
                                        floatToString(configMaxScriptMemory, 2),"kb)"];
                                    eject = TRUE;
                                }
                                else if (configMaxScriptTime != -1 && llList2Float(details, 1) * 1000000.0 > configMaxScriptTime) {
                                    reason = (string)["script time (",
                                        floatToString(llList2Float(details, 1) / 1000000.0, 3),"/",
                                        floatToString(configMaxScriptTime, 3),"μs)"];
                                    eject = TRUE;
                                }
                                else if (configMaxScriptCount != -1 && llList2Integer(details, 2) > configMaxScriptCount) {
                                    reason = (string)["script count (",llList2Integer(details, 2),"/",configMaxScriptCount,")"];
                                    reason = "script count";
                                    eject = TRUE;
                                }
                                else if (configMaxRenderWeight != -1 && llList2Float(details, 3) > configMaxRenderWeight) {
                                    reason = (string)["render weight (",
                                        floatToString(llList2Float(details, 3), 1),"/",
                                        floatToString(configMaxRenderWeight, 1),")"];
                                    eject = TRUE;
                                }
                                else if (configMaxAttachmentInventory != -1 && llList2Integer(details, 4) > configMaxAttachmentInventory) {
                                    reason = (string)["attachment inventory (",llList2Integer(details, 4),"/",configMaxAttachmentInventory,")"];
                                    eject = TRUE;
                                }
                            }
                        }
                    }
                    
                    if (eject && !~pendingEjection){
                        securityEjectQueue += [id, reason, 0, llGetUnixTime()];
                    }
                    else if ((!eject || !observe) && ~pendingEjection && !~pendingDataChecks){
                        if(!observe)
                            reason = "left area";
                        else
                            reason = llList2String(securityEjectQueue, pendingEjection + 1);
                        securityEjectQueue = llDeleteSubList(securityEjectQueue, pendingEjection, pendingEjection + 3);
                        llDialog(id, (string)[
                            "📉️ All Clear️",
                            "\nYou are no in volation of the rules.",
                            "\n\tResolved: ",reason
                            ], ["Ok"], -100);
                    }
                }
            }
        }
        
        if(llGetUnixTime() - lastSecurityPresenceCleanup > 15){
            lastSecurityPresenceCleanup = llGetUnixTime();
            integer i = ~llGetListLength(securityPresence);
            key id;
            while(++i){
                id = llList2Key(securityPresence, i);
                if(!llGetListLength(llGetObjectDetails(id, [OBJECT_ROOT])))
                    securityPresence = llDeleteSubList(securityPresence, i, i);
            }
        }
        
        if(llGetListLength(securityEjectQueue)){
            integer i;
            integer n = llGetListLength(securityEjectQueue);
            key id;
            string reason;
            integer time;
            integer mask;
            integer now = llGetUnixTime();
            integer isOwner;
            integer overOurLand;
            integer canEject;
            integer isDwelling;
            integer isWaiting;
            integer totalWait;
            integer find;
            integer result;
            string announcement;
            string message;
            list tokens;
            string token;
            string value;
            list parts;
            for(; i<n; i+=4){
                id = llList2Key(securityEjectQueue, i);
                reason = llList2String(securityEjectQueue, i+1);
                mask = llList2Integer(securityEjectQueue, i+2);
                time = llList2Integer(securityEjectQueue, i+3);
                
                // build time calculation
                totalWait = 0;
                if (configEjectDelay != -1)
                    totalWait += configEjectDelay;
                if (configEjectDelayAllowedDwell != -1)
                    totalWait += configEjectDelayAllowedDwell;
                
                isOwner = id == securitySuperAdmin;
                overOurLand = llOverMyLand(id);
                canEject = overOurLand || configUseEstate;
                isWaiting = totalWait != 0 && now - time < totalWait;
                isDwelling = configEjectDelayAllowedDwell != -1 && now - time < configEjectDelayAllowedDwell;
                
                if(!isOwner && canEject && !isWaiting){
                    // inform avatar of actions being taken
                    announcement = (string)[llList2String(["","DRYRUN | "], configDryRun), "You are being ejected from this land. Reason: ", reason];
                    llRegionSayTo(id, 0, announcement);
                    
                    if(!configDryRun){
                        // determine removal mechanism
                        if(configEjectWithTP) llTeleportAgentHome(id);
                        else llEjectFromLand(id);
                        
                        // determine if we need to modify the ban list
                        if(configTimeBan >= 0 && !configUseEstate && overOurLand) {
                            llAddToLandBanList(id, configTimeBan);
                        } else if(configUseEstate){
                            result = llManageEstateAccess(ESTATE_ACCESS_BANNED_AGENT_ADD, id);
                            if(!result){
                                securityEstateFailures++;
                            }
                        }
                    }
                    
                    // determine if we need to remove the agent from our local cache
                    find = llListFindList(securityPresence, [id]);
                    if(~find)
                        securityPresence = llDeleteSubList(securityPresence, find, find);
                    
                    // alert event based on config
                    announcement = (string)["secondlife:///app/agent/",id,"/about has been ejected from this land. Reason: ",reason];
                    if (configVerbose == "public" || configVerbose == "yes")
                        llSay(0, announcement);
                    else if (configVerbose == "owner")
                        llRegionSayTo(securitySuperAdmin, 0, announcement);
                    else if (configVerbose == "broadcast"){
                        list avs = llGetAgentList(4, []);
                        key id;
                        while(llGetListLength(avs)){
                            id = llList2Key(avs, 0);
                            avs = llDeleteSubList(avs, 0, 0);
                            if(llOverMyLand(id))
                                llRegionSayTo(id, 0, announcement);
                        }  
                    }
                    
                    securityEjectQueue = llDeleteSubList(securityEjectQueue, i, i+3);
                    i -= 4;
                    n -= 4;
                }
                else if (isWaiting && !isDwelling && !(mask & 4) && configEjectDelayMessage != ""){
                    securityEjectQueue = llListReplaceList(securityEjectQueue, [mask | 4], i+2, i+2);
                    message = configEjectDelayMessage;
                    tokens = [
                        "{username}", llGetUsername(id),
                        "{delay}", configEjectDelay,
                        "{reason}", reason
                    ];
                    while(llGetListLength(tokens)){
                        token = llList2String(tokens, 0);
                        value = llList2String(tokens, 1);
                        tokens = llDeleteSubList(tokens, 0, 1);
                        parts = llParseStringKeepNulls(message, [], [token]);
                        while(~(find=llListFindList(parts, [token])))
                            parts = llListReplaceList(parts, [value], find, find);
                        message = (string)parts;
                    }
                    llDialog(id, (string)[
                        "⚠️ Proximity Alert ⚠️",
                        "\nYou have entered a restricted space.",
                        "\n\tViolation: ",reason,
                        "\n\n> ",message
                        ], ["Ok"], -100);
                }
                else if ((!canEject || isOwner) && !isWaiting) {
                    securityEjectQueue = llDeleteSubList(securityEjectQueue, i, i+3);
                    i -= 4;
                    n -= 4;
                }
            }
        }
        
        if (configShowHoverText){
            llMessageLinked(LINK_THIS, 0, 
                llList2Json(JSON_ARRAY, ["renderText"]),
                "");
        }
    }
    
    dataserver(key id, string data){
        if(id == ncReader){
            if (data == EOF){
                ncBusy = FALSE;
                
                if (ncName == "config"){
                    // Validation settings
                    if (configTimeBan < 0) configTimeBan = -1;
                    if (configTimeBan > 144) configTimeBan = 144;
                    
                    if(!~llListFindList(["silent","public","owner","no","yes"], [configVerbose])) configVerbose = "silent";
                    
                    if (configRange < -1) configRange = -1;
                    
                    if (configMinAge < -1) configMinAge = -1;
                    
                    // object details limiters
                    if (configMaxScriptMemory < 0) configMaxScriptMemory = -1;
                    if (configMaxScriptTime < 0) configMaxScriptTime = -1;
                    if (configMaxScriptCount < 0) configMaxScriptCount = -1;
                    if (configMaxRenderWeight < 0) configMaxRenderWeight = -1;
                    if (configMaxAttachmentInventory < 0) configMaxAttachmentInventory = -1;
                    
                    // warning delays
                    if (configEjectDelay <= 0) configEjectDelay = -1;
                    else if (configEjectDelay > 60) configEjectDelay = 60;
                    
                    // waiting before ejecting
                    if (configEjectDelayAllowedDwell < 0) configEjectDelayAllowedDwell = -1;
                    else if (configEjectDelayAllowedDwell > 60) configEjectDelayAllowedDwell = 60;
                    
                    // Display settings
                    if (configTimeBan != -1)
                        llOwnerSay((string)["👉 Set to ban from parcel for ",floatToString(configTimeBan, 2)," hours"]);
                    else
                        llOwnerSay((string)["👉 Set to never ban from parcel"]);
                    
                    llOwnerSay((string)["👉 Verbosity set to ", configVerbose]);
                    
                    if (configRange == -1)
                        llOwnerSay((string)["👉 Set to monitor the entire region"]);
                    else
                        llOwnerSay((string)["👉 Set to monitor all agents within", floatToString(configRange, 2), "m"]);
                    
                    if (llGetListLength(configRestrictZones))
                        llOwnerSay((string)["👉 Loaded ", llGetListLength(configRestrictZones)/3, " zones"]);
                        
                    if (configEjectDelayAllowedDwell != -1)
                        llOwnerSay((string)["👉 Set to wait ",configEjectDelayAllowedDwell, " seconds before warning avatar"]);
                        
                    if (configEjectDelay != -1)
                        llOwnerSay((string)["👉 Set to warn avatar ", configEjectDelay, " seconds before ejecting"]);
                        
                    if (configMinAge != -1)
                        llOwnerSay((string)["👉 Set only allow avatars older than ", configMinAge, " days"]);
                        
                    if (configMaxScriptMemory != -1)
                        llOwnerSay((string)["👉 Set to eject avatars with more than ", floatToString(configMaxScriptMemory, 2), " kb script memory"]);
                        
                    if (configMaxScriptTime != -1)
                        llOwnerSay((string)["👉 Set to eject avatars with more than ", floatToString(configMaxScriptTime, 3), "μs script time"]);
                        
                    if (configMaxScriptCount != -1)
                        llOwnerSay((string)["👉 Set to eject avatars with more than ", configMaxScriptCount, " scripts"]);
                        
                    if (configMaxRenderWeight != -1)
                        llOwnerSay((string)["👉 Set to eject avatars with a render weight higher than ", floatToString(configMaxRenderWeight, 2)]);
                        
                    if (configMaxAttachmentInventory != -1)
                        llOwnerSay((string)["👉 Set to eject avatars with attachment inventory including more than ", configMaxAttachmentInventory, " items"]);
                        
                    if (configMaxAvatarHeight != -1)
                        llOwnerSay((string)["👉 Set to eject avatars are taller than ", floatToString(configMaxAvatarHeight, 2), "m"]);
                        
                    if(configEjectOnGroup)
                        llOwnerSay((string)["👉 Set to eject when an avatar has the wrong group"]);
                    if(configEjectOnFlying)
                        llOwnerSay((string)["👉 Set to eject when an avatar is flying"]);
                    if(configEjectOnAfk)
                        llOwnerSay((string)["👉 Set to eject when an avatar is afk"]);
                    if(configEjectOnNoPayment)
                        llOwnerSay((string)["👉 Set to eject when an avatar has no payment information"]);
                    if(configEjectOnUnusedPayment)
                        llOwnerSay((string)["👉 Set to eject when an avatar has unused payment information"]);
                    if(configEjectWithTP)
                        llOwnerSay((string)["👉 Set to eject by teleporting the avatar home"]);
                    else
                        llOwnerSay((string)["👉 Set to eject by removing the avatar from the parcel"]);
                    
                    // Warn of conflicting configuration items
                    if (configUseEstate && configTimeBan != -1)
                        llOwnerSay((string)["⚠️ Conflict (useEstate, timeToBan): Estate ban does not support temporary bans."]);
                    
                    if (configRange != -1 && configRange < 1)
                        llOwnerSay((string)["⚠️ Warning (scanRange): Very small distance selected. Did you mean to disable?"]);
                    
                    if (configRange != -1 && llGetListLength(configRestrictZones))
                        llOwnerSay((string)["⚠️ Conflict (scanRange, restrictZones): Zone restriction is not compatible with scanRange config."]);
                    
                    if (
                        llListStatistics(LIST_STAT_MAX, [
                            configMinAge,
                            configMaxScriptMemory,
                            configMaxScriptTime,
                            configMaxScriptCount,
                            configMaxRenderWeight,
                            configMaxAttachmentInventory
                            ]) == -1
                        && llListStatistics(LIST_STAT_MAX, [
                            configEjectOnGroup,
                            configEjectOnFlying,
                            configEjectOnAfk,
                            configEjectOnNoPayment,
                            configEjectOnUnusedPayment
                            ]) == 0
                        )
                        llOwnerSay((string)["⚠️ Warning: No restrictions defined, no avatars will be evaluated."]);

                    if(configDryRun)
                        llOwnerSay((string)["⚠️ Warning: Dry Run enabled, no avatars will be ejected."]);
                    
                }
                else if (ncName == "whitelist"){
                    llOwnerSay((string)["👉 Added ",llGetListLength(configWhitelist)," avatars to the whitelist"]);
                }
                
                // load more settings files
                llMessageLinked(LINK_THIS, 0, 
                    llList2Json(JSON_ARRAY, ["loadSettings"]),
                    "");
            }
            else {
                if(ncLine % 4 == 0)
                    llMessageLinked(LINK_THIS, 0, 
                        llList2Json(JSON_ARRAY, ["renderText", TRUE]),
                        "");
                
                // read next notecard line
                ncLine++;
                ncReader = llGetNotecardLine(ncName, ncLine);
                
                if (ncName == "config"){
                    // parse data
                    data = llStringTrim(data, STRING_TRIM);
                    
                    // ignore comments
                    if (llGetSubString(data, 0, 1) != "//"){
                    
                        list tokens = llParseString2List(data, [","], []);
                        string var = llToLower(llStringTrim(llList2String(tokens, 0), STRING_TRIM));
                        string val = llStringTrim(llDumpList2String(llDeleteSubList(tokens, 0, 0), ","), STRING_TRIM);
                        
                        list optionsBoolTrue = ["yes", "1", "true"];
                        
                        if (var == "timeban" || var == "timetoban") configTimeBan = (float)val;
                        else if (var == "verbose" || var == "verbosity") configVerbose = llToLower(val);
                        else if (var == "range" || var == "scanrange") configRange = (float)val;
                        else if (var == "hover-text" || var == "showhovertext") 
                            configShowHoverText = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "age" || var == "minage") configMinAge = (integer)val;
                        else if (var == "wrong-group-eject" || var == "ejectongroup") 
                            configEjectOnGroup = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "flying-eject" || var == "ejectonflying") 
                            configEjectOnFlying = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "afk-eject" || var == "ejectonafk") 
                            configEjectOnAfk = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "ejectonnopayment") 
                            configEjectOnNoPayment = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "ejectonunusedpayment") 
                            configEjectOnUnusedPayment = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "ejectwithtp")
                            configEjectWithTP = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "maxscriptmemory")
                            configMaxScriptMemory = (float)val;
                        else if (var == "maxscripttime")
                            configMaxScriptTime = (float)val;
                        else if (var == "maxscriptcount")
                            configMaxScriptCount = (integer)val;
                        else if (var == "maxrenderweight")
                            configMaxRenderWeight = (float)val;
                        else if (var == "maxavatarheight")
                            configMaxAvatarHeight = (float)val;
                        else if (var == "maxattachmentinventory")
                            configMaxAttachmentInventory = (integer)val;
                        else if (var == "useestate") 
                            configUseEstate = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                        else if (var == "ejectdelay")
                            configEjectDelay = (integer)val;
                        else if (var == "ejectdelaymessage")
                            configEjectDelayMessage = val;
                        else if (var == "ejectdelayalloweddwell")
                            configEjectDelayAllowedDwell = (integer)val;
                        else if (var == "restrictzone") {
                            val = (string)llParseStringKeepNulls(val, [" "], []);
                            val = llGetSubString(val, 1, -2);
                            tokens = llParseString2List(val, [">,<",","], []);
                            configRestrictZones += [
                                <   (float)llList2String(tokens, 0),
                                    (float)llList2String(tokens, 1),
                                    (float)llList2String(tokens, 2)
                                >,
                                <   (float)llList2String(tokens, 3),
                                    (float)llList2String(tokens, 4),
                                    (float)llList2String(tokens, 5)
                                >,
                                <   (float)llList2String(tokens, 6),
                                    (float)llList2String(tokens, 7),
                                    (float)llList2String(tokens, 8),
                                    (float)llList2String(tokens, 9)
                                >
                            ];
                        }
                        else if (var == "dryrun") 
                            configDryRun = !!~llListFindList(optionsBoolTrue, [llToLower(val)]);
                    }
                }
                else if(ncName == "whitelist"){
                    // add to whitelist if not already exists
                    id = (key)data;
                    if (llStringLength(data) == 36){
                        if(!~llListFindList(configWhitelist, [id]))
                            configWhitelist += id;
                    }
                }
            }
        }
        else {
            // not loading a notecard, check if this originates from an async verification task
            integer find = llListFindList(securityDataChecks, [id]);
            if(~find){
                id = llList2Key(securityDataChecks, find+1);
                string type = llList2String(securityDataChecks, find+2);
                securityDataChecks = llDeleteSubList(securityDataChecks, find, find+2);
                integer eject;
                string reason = "unknown";
                
                if (type == "pay"){
                    integer mask = (integer)data;
                    if(configEjectOnNoPayment && !(mask & PAYMENT_INFO_ON_FILE)){
                        eject = TRUE;
                        reason = "payment info (missing)";
                    }
                    else if(configEjectOnUnusedPayment && !(mask & PAYMENT_INFO_USED)){
                        eject = TRUE;
                        reason = "payment info (unused)";
                    }
                }
                else if(type == "age"){
                    integer days = date2days(llGetTimestamp());
                    days -= date2days(data);
 
                    if(~configMinAge && days < configMinAge) {
                        eject = TRUE;
                        reason = (string)["account too new (",days,"/",configMinAge,"days)"];
                    }
                }
                
                if (eject){
                    securityEjectQueue += [id, reason, 0, llGetUnixTime()];
                }
            }
        }
    }
        
    link_message(integer sender, integer num, string json, key id){
        list parts = llJson2List(json);
        string cmd = llList2String(parts, 0);
        parts = llDeleteSubList(parts, 0, 0);
        if(cmd == "loadSettings"){
            if (securityReady)
                return; // already setup
                
            if (ncBusy) {
                ncQueue += parts;
                return; // queue reads
            }
            ncQueue += parts;
            string name = llList2String(ncQueue, 0);
            ncQueue = llDeleteSubList(ncQueue, 0, 0);
            if(llGetInventoryType(name) == INVENTORY_NOTECARD){
                ncBusy = TRUE;
                ncName = name;
                ncLine = 0;
                ncReader = llGetNotecardLine(ncName, ncLine);
                llOwnerSay("⏳ Loading notecard '"+ncName+"'...");
            } else if (llGetListLength(ncQueue))
                llMessageLinked(LINK_THIS, 0, 
                    llList2Json(JSON_ARRAY, ["loadSettings"]),
                    "");
            else {
                securityReady = TRUE;
                llSetTimerEvent(2.5);
                llOwnerSay((string)["💾 Memory used ",llRound(llGetUsedMemory()/1024.0),"kb"]);
                llOwnerSay((string)["📈 Took ",llGetTime(), " seconds"]);
                llOwnerSay("✔️ System Ready");
                llMessageLinked(LINK_THIS, 0, 
                    llList2Json(JSON_ARRAY, ["renderText", TRUE]),
                    "");
            }
        }
        else if (cmd == "renderText"){
            integer override = (integer)llList2String(parts, 0);
            list text;
            vector color = <1,1,1>;
            if (!securityReady){
                text = [
                    llGetObjectName(),
                    "\nby BinaryArchitect",
                    "\n----------------",
                    "\nSetting up system..."
                    ];
                color = <1,0.5,0>;
                if (ncBusy){
                    text += (string)["\nReading notecard '",ncName,"' @ ",ncLine];
                    text += (string)["\nMemory used ",llRound(llGetUsedMemory()/1024.0),"kb"];
                }
            }
            else if (configShowHoverText || override){
                text = [
                    llGetObjectName(),
                    "\nby BinaryArchitect",
                    "\n----------------"
                    ];
                if (configDryRun){
                    text += "\nDRY RUN: Will not eject";
                    color = <0,0,1>;
                }
                else if (configUseEstate) {
                    color = <0,0.8,0>;
                    text += (string)["\nSystem Active"];
                    text += (string)["\nEstate Mode"];
                    if (securityEstateFailures > 0)
                        text += (string)["\nFailures: ", securityEstateFailures];
                } else if(llOverMyLand(llGetKey())){
                    color = <0,1,0>;
                    text += (string)["\nSystem Active"];
                } else {
                    color = <1,0,0>;
                    text += (string)["\nNot setup"];
                    text += (string)["\nPlease fix group permissions (deed to group)"];
                }
            }
            string hash = llSHA1String((string)(text+[color]));
            if(hash != lastDisplay){
                lastDisplay = hash;
                integer linkNumber = 0;
                if (llGetNumberOfPrims() > 1)
                    linkNumber = 1;
                llSetLinkPrimitiveParamsFast(linkNumber, [
                    PRIM_TEXT, (string)text, color, 0.9
                    ]);
            }
        }
    }
}
