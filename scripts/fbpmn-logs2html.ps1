#!/usr/bin/env pwsh

$logs = Get-ChildItem -Name -Include *.log 
foreach ($f in $logs) {
    $ff = $f -Replace ".log", ""
    fbpmn log2html $ff $ff
}
