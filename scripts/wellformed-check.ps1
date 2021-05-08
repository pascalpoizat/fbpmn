#!/usr/bin/env pwsh

# wellformed-check model.bpmn
# Translate a model and check its well-formedness
# Beware: changing PWSWellFormed!WellFormedness requires changing ALLASSUME here.

if ($env:FBPMN_HOME.Length -eq 0) {
    Write-Host "$env:FBPMN_HOME is not set"; exit 1
}
if (-NOT(Test-Path $env:FBPMN_HOME/theories/tla)) {
    Write-Host "wrong $env:FBPMN_HOME (theories/tla not found)"; exit 1
} #log si $env:FBPMN_HOME / theories/tla n'est pas un répertoire
if ($env:TLA2TOOLS_HOME.Length -eq 0 ) {
    Write-Host "$env:TLA2TOOLS_HOME is no set"; exit 1
}
if (-NOT(Test-Path $env:TLA2TOOLS_HOME/tla2tools.jar)) {
    Write-Host "wrong $env:TLA2TOOLS_HOME (tla2tools.jar not found)"; exit 1
} #log si $env:TLA2TOOLS_HOME / tla2tools.jar n'est pas un fichier ordinaire

$runtlc = { 
    param($a = "", $b = 1)
    java -XX:+UseParallelGC -classpath $env:TLA2TOOLS_HOME/tla2tools.jar tlc2.TLC -deadlock $a -workers $b
}

ALLASSUME='ASSUME WF!C1_StartNoIncomingEdge\nASSUME WF!C2_EndNoOutgoingEdge\nASSUME WF!C3_SubProcessUniqueStart\nASSUME WF!C4_NoProcessInSubProcess\nASSUME WF!C5_ProcessNode\nASSUME WF!C6_NoLoopingEdge\nASSUME WF!C7_NoNodeIsolation\nASSUME WF!C8_DefaultSeqFlow\nASSUME WF!C9_NoIncomingMessageFlow\nASSUME WF!C10_NoOutgoingMessageFlow\nASSUME WF!C11_MessageFlowDifferentProcesses\nASSUME WF!C12_EBTwoOutgoingEdges\nASSUME WF!C13_ParEb_NoConditional\nASSUME WF!C14_EXOR_NextElements\nASSUME WF!C15_OrXor_OutgoingEdges\nASSUME WF!C16_MessageFlowEdge\nASSUME WF!C17_ReceiveIncomingEdge\nASSUME WF!C18_SendOutgoingEdge'

if ( $args.Length -ne 1 ) {
    Write-Host ` (Get-ChildItem $args[0]).Basename ` '<model>' '[#workers]'
    exit 1
}

$fullpath = $args[0] #strip extension
$model = (Get-ChildItem $fullpath).Basename
$parent = [System.IO.Path]::GetTempPath() #pour obtenir le bon chemin vers tmp
$guid = [guid]::NewGuid()
$name = $model + "." + (([string]$guid).Replace("-", "")).Substring(0, 5)
$dir = New-Item -ItemType Directory -Path (Join-Path $parent $name)
#$dir = New-Item -Path  /tmp/$model.XXXXX -ItemType Directory

if (-NOT(Test-Path $fullpath)) {
    Write-Host "$fullpath.bpmn not found."
    exit 1
}

Copy-Item $fullpath $dir
if (Test-Path "$fullpath.constraint") { Copy-Item "$fullpath.constraint" $dir }
Set-Location $dir
fbpmn bpmn2tla $model $model >/dev/null

if (-NOT(Test-Path "$model.tla")) {
    Write-Host "model transformation failed"
    exit 1
}

# Copy verification files
Copy-Item (Get-ChildItem $env:FBPMN_HOME/theories/tla -Filter PWS*.tla) $dir 
Copy-Item (Get-ChildItem $env:FBPMN_HOME/theories/tla -Filter Network*.tla) $dir 

# add a spec with no next
sed -e 's/INSTANCE PWSSemantics/INSTANCE PWSSemantics\nSpecEmpty == Init \/\\ ()(UNCHANGED <<nodemarks, edgemarks, net>>)_var/'  "$model.tla" >"${model}2.tla"

# Remove ASSUME WellFormedness and put in place individual assumes
sed -e "s/ASSUME WF!WellFormedness/$ALLASSUME/" "${model}2.tla" >"$model.tla"

Write-Host "SPECIFICATION SpecEmpty" >"${model}.cfg"
$log = "$model.log"

& $runtlc $model >$log 2>&1

if (Select-String -Quiet 'Error: Assumption.*is false' $log) {
    Write-Host "( ) $model : bad model. Check $dir"
    $erraur = `Select-String 'Error: Assumption.*is false' $log`
    linenum=`expr "$erraur" : '.*line \((0-9)*\),'`
        msg=`head -$linenum ${model}.tla | tail -1`
    Write-Host "    failed: $msg"
}
else {
    if (Select-String -Quiet "No error has been found" $log) {
        Write-Host "(X) $model : Well-Formed"
    }
    else { 
        Write-Host "Unexpected log, check $dir/$log"
    }
}
