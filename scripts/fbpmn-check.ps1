#!/usr/bin/env pwsh

# For each configuration Config/Prop*cfg (property to check) and each
# network Config/Network*, run tlc and analyse the results.

# runtlc="java -classpath /opt/tla --add-modules java.activation tlc2.TLC -deadlock"
$runtlc = { 
    param($a = "", $b = 1)
    java -XX:+UseParallelGC -classpath $env:TLA2TOOLS_HOME/tla2tools.jar tlc2.TLC -deadlock $a -workers $b
}
################

$parse_stat = {
    param($a = "", $b = "")
    if ($a -match '(\d*) states generated') {
        $transitions = $matches[1] 
    }
    if ($a -match '(\d*) distinct states found') {
        $states = $matches[1] 
    }
    if ($b -match 'The depth of the complete state graph search is (\d*)') {
        $depth = $matches[1] 
    }
    Write-Host "     states=$states trans=$transitions depth=$depth"
}

function New-Dir {
    param ($fullpath, $model)
    $parent = [System.IO.Path]::GetTempPath() 
    $guid = [guid]::NewGuid()
    $name = $model + "." + (([string]$guid).Replace("-", "")).Substring(0, 5)
    $dir = New-Item -ItemType Directory -Path (Join-Path $parent $name)
    return $dir
} 

################

if ($args.Length -eq 0 -or $args.Length -gt 2) {
    Write-Host ` (Get-ChildItem $PSCOMMANDPATH).Basename ` '<model>' '[#workers]' 
    exit 1
}

if ($args.Length -eq 2 ) {
    $workers = $args[1]
}
else {
    $workers = 1
}

if (-NOT (which fbpmn) > /dev/null) {
    Write-Host "fbpmn is not found in the PATH, please install it"
    exit 1
}

if (-NOT (which java) > /dev/null) {
    Write-Host "java is not found in the PATH, please install it"
    exit 1
}

if ($env:FBPMN_HOME.Length -eq 0) {
    Write-Host "$env:FBPMN_HOME is not set"; exit 1
}
if (-NOT(Test-Path $env:FBPMN_HOME/theories/tla)) {
    Write-Host "wrong $env:FBPMN_HOME (theories/tla not found)"; exit 1
} 
if ($env:TLA2TOOLS_HOME.Length -eq 0 ) {
    Write-Host "$env:TLA2TOOLS_HOME is no set"; exit 1
}
if (-NOT(Test-Path $env:TLA2TOOLS_HOME/tla2tools.jar)) {
    Write-Host "wrong $env:TLA2TOOLS_HOME (tla2tools.jar not found)"; exit 1
} 

$fullpath = $args[0]
$model = (Get-ChildItem $fullpath).Basename
$dir = New-Dir $fullpath $model

if (-NOT(Test-Path $fullpath)) {
    Write-Host "$fullpath.bpmn not found."
    exit 1
}

Write-Host "Working in $dir with $workers worker(s)"

# TransfoRemove-Item the BPMN model into TLA
Copy-Item $fullpath $dir
if (Test-Path "$fullpath.constraint") { Copy-Item "$fullpath.constraint" $dir }
Set-Location $dir
fbpmn bpmn2tla $model $model

if (-NOT(Test-Path "$model.tla")) {
    Write-Host "model transfoRemove-Itemation failed"
    exit 1
}

# Copy verification files
Copy-Item (Get-ChildItem $env:FBPMN_HOME/theories/tla -Filter PWS*.tla) $dir -Recurse -Force
Copy-Item (Get-ChildItem $env:FBPMN_HOME/theories/tla -Filter Network*.tla) $dir -Recurse -Force
Copy-Item $env:FBPMN_HOME/theories/tla/Configs $dir -Recurse -Force


# First, use StatsBPMN to print some infoRemove-Itemation on the size of the BPMN model.
Copy-Item $env:FBPMN_HOME/theories/tla/StatsBPMN.cfg -Force
(Get-Content $env:FBPMN_HOME/theories/tla/StatsBPMN.tla) -Replace ("INSTANCE.*$", "INSTANCE $model") > StatsBPMN.tla
& $runtlc "$dir/StatsBPMN.tla" | Select-String "Processes="
Remove-Item states -Recurse -Force

# For each configuration Config/*cfg (property to check) and each network Config/Network,
# build the files Network.tla and model.cfg
$file_network = Get-ChildItem -Path Configs -Name -Include Network*.tla 
$file_cfg = Get-ChildItem -Path Configs -Name -Include Prop*.cfg 
foreach ($network in $file_network) {
    $networkname = (Get-ChildItem Configs/$network).Basename
    Copy-Item Configs/$network Network.tla
    Write-Host "---------- $networkname ----------"
    foreach ($cfg in $file_cfg) {
        $cfgname = (Get-ChildItem Configs/$cfg).Basename
        $log = "$model.$networkname.$cfgname.log"
        Copy-Item Configs/$cfg "$model.cfg"
        if (Test-Path "$model.constraint") { 
            Get-Content "$model.constraint" >> "$model.cfg"; 
        }
        & $runtlc $model $workers > $log
        Remove-Item states -Recurse -Force
        if (Select-String -Quiet "Error: Assumption.*is false" -Path $log) {
            Write-Host "  ! PANIC: bad model (assume failed)"
        }
        else {
            if (Select-String -Quiet "No error has been found" -Path $log) {
                Write-Host "[X] $cfgname"
            }
            else {
                Write-Host "[ ] $cfgname"
            }
            $stat1 = Select-String "^[0-9]* states generated.*0 states left on queue" -Path $log
            $stat2 = Select-String "The depth of the complete state graph" -Path $log
            & $parse_stat "$stat1" "$stat2"
        }
    }
}

Write-Host "done."

