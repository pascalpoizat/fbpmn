#!/usr/bin/env pwsh


BeforeAll { 
    . fbpmn-private/scripts/fbpmn-check.ps1
    
    function F1 {
        param ($expected, $observed)
        if ([string](Get-Content $expected | Select-Object -Skip 2) -eq [string](Get-Content $observed | Select-Object -Skip 3 | Select-Object -SkipLast 1)) {
            return $true
        } 
        return $false
    }

    function F2 {
        param ($model, $expected, $observed)
        $json_expected = Get-Content $expected | ConvertFrom-Json
        $Network = $json_expected.$model.psobject.properties.name 
        $Prop = $json_expected.$model.($Network[0]).psobject.properties.name 
        $Result = $json_expected.$model.($Network[0]).($Prop[0]).psobject.properties.name
        $json_observed = Get-Content $observed | ConvertFrom-Json
        
        for ($i = 0 ; $i -le (($json_expected.$model.psobject.properties.name).count - 1) ; $i++ ) {
            for ($j = 0 ; $j -le (($json_expected.$model.($Network[$i]).psobject.properties.name).count - 1) ; $j++) {
                for ($k = 0 ; $k -le (($json_expected.$model.($Network[$i]).($Prop[$j]).psobject.properties.name).count - 1) ; $k++) {
                    if (-NOT($json_observed.$model.($Network[$i]).($Prop[$j]).($Result[$k]) -eq $json_expected.$model.($Network[$i]).($Prop[$j]).($Result[$k]))) {
                        return $false
                    }
                }
            }
        }
        return $true    
    }
}



Describe 'fbpmn-check' {
    Context "Usage" {
        Context "workers" {
            It 'Good exit for wrong args.Length' {
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2 3 
                $LASTEXITCODE | Should -Be 1
            } 
            It 'No args -> workers = 1' {
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn *> /tmp/e033MBE.out
                $a = Select-String "Working in" -Path /tmp/e033MBE.out -NoEmphasis 
                $a -match "with (\d)"
                $matches[1] | Should -Be 1
            } 
            It 'Correct args.Length -> workers = args[1]' {
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 3 *> /tmp/e033MBE.out2
                $a = Select-String "Working in" -Path /tmp/e033MBE.out2 -NoEmphasis 
                $a -match "with (\d)"
                $matches[1] | Should -Be 3 
            } 
        }
        Context "commands java and fbpmn" {
            It 'java not found' {
                $OLD_PATH = $env:PATH
                $env:PATH = $env:PATH -replace (":/usr/bin:", ":")
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
                $LASTEXITCODE | Should -Be 1
                $env:PATH = $OLD_PATH
            }
            It 'fbpmn not found' {
                $OLD_PATH = $env:PATH
                $env:PATH = $env:PATH -replace (":/home/malinvaud/fbpmn-0.3.4-linux.x86_64:", ":")
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
                $LASTEXITCODE | Should -Be 1
                $env:PATH = $OLD_PATH 
            }
        }
        Context "env:variables" {
            It 'FBPMN_HOME not set' {
                $OLD_FBPMN_HOME = $env:FBPMN_HOME
                $env:FBPMN_HOME = ''
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
                $LASTEXITCODE | Should -Be 1
                $env:FBPMN_HOME = $OLD_FBPMN_HOME
            }
            It 'Wrong FBPMN_HOME' {
                $OLD_FBPMN_HOME = $env:FBPMN_HOME
                $env:FBPMN_HOME = '/home/malinvaud/Documents/L3' #associer un directory qui n'est pas FBPMN_HOME
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
                $LASTEXITCODE | Should -Be 1
                $env:FBPMN_HOME = $OLD_FBPMN_HOME
            }
            It 'TLA2TOOLS_HOME not set' {
                $OLD_TLA2TOOLS_HOME = $env:TLA2TOOLS_HOME
                $env:TLA2TOOLS_HOME = ''
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
                $LASTEXITCODE | Should -Be 1
                $env:TLA2TOOLS_HOME = $OLD_TLA2TOOLS_HOME
            }
            It 'Wrong TLA2TOOLS_HOME ' {
                $OLD_TLA2TOOLS_HOME = $env:TLA2TOOLS_HOME
                $env:TLA2TOOLS_HOME = '/home/malinvaud/Documents/L3' #associer un directory qui n'est pas TLA2TOOLS_HOME
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
                $LASTEXITCODE | Should -Be 1
                $env:TLA2TOOLS_HOME = $OLD_TLA2TOOLS_HOME
            }
        }
    }
    Context "Compare with expected" {
        <#It "V1" {
            $r = 0
            $f_bpmn = New-Object System.Collections.Generic.List[string]  
            $f = Get-Content ("$env:FBPMN_HOME/scripts/tests/config-files.json") | ConvertFrom-Json                                      
            foreach ($g in $f.psobject.properties.name) {
                if ($f."$g") { 
                    $f_bpmn.Add([string]$g) 
                }
            }
            $model
            foreach ($f in $f_bpmn) {
                $fullpath = "$env:FBPMN_HOME/models/bpmn-origin/src/$f"
                $model = (Get-ChildItem -Path $fullpath).BaseName
                fbpmn-check.ps1 $fullpath 1 *> "/tmp/$model.observed" 
                if (-NOT(F1 "$env:FBPMN_HOME/models/bpmn-origin/expected/$model.expected" "/tmp/$model.observed")) {
                    $r++
                } 
            }
            $r | Should -Be 0
        }#>
        It "V2" { 
            $r = 0
            $f_bpmn = New-Object System.Collections.Generic.List[string]  
            $f = Get-Content ("$env:FBPMN_HOME/scripts/tests/config-files.json") | ConvertFrom-Json                                      
            foreach ($g in $f.psobject.properties.name) {
                if ($f."$g") { 
                    $f_bpmn.Add([string]$g) 
                }
            }
            foreach ($f in $f_bpmn) {
                $fullpath = "$env:FBPMN_HOME/models/bpmn-origin/src/$f"
                $model = (Get-ChildItem -Path $fullpath).BaseName
                fbpmn-check.ps1 $fullpath *> WHERE 
                if (-NOT(F2 $model "$env:FBPMN_HOME/models/bpmn-origin/expected/$model.json" "$model.json")) {
                    $r++                    
                } 
            }
            $r | Should -Be 0
        }
    }
    Context "Test-Path failed" {
        It "BPMN don't exists" {
            fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/idontexist.bpmn 2  
            $LASTEXITCODE | Should -Be 1
        }
    }
}
