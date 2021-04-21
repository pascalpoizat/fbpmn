#!/usr/bin/env pwsh

$logs = Get-ChildItem -Name -Include *.log 
foreach ($f in $logs) {
    $ff = $f -Replace ".log", ""
    fbpmn log2dot $ff $ff
    dot -Tpdf -o "$ff.pdf" "$ff.dot"; 
}


