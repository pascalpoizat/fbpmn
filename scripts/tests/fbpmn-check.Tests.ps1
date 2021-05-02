#!/usr/bin/env pwsh


BeforeAll { 
    . fbpmn-private/scripts/fbpmn-check.ps1
    
    function F {
        param ($expected, $observed)
        if ([string](Get-Content $expected | Select-Object -Skip 2 | Select-String "states" -NotMatch) -eq [string](Get-Content $observed | Select-Object -Skip 3 | Select-Object -SkipLast 1 | Select-String "states" -NotMatch)) {
            return $true
        } 
        return $false
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
                $env:FBPMN_HOME = '' #associer un directory qui n'est pas FBPMN_HOME
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
                $env:TLA2TOOLS_HOME = '' #associer un directory qui n'est pas TLA2TOOLS_HOME
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2
                $LASTEXITCODE | Should -Be 1
                $env:TLA2TOOLS_HOME = $OLD_TLA2TOOLS_HOME
            }
        }
    }
    <#Context "Compare with expected" {
        It "V1" {
            $r = 0
            $f_bpmn = New-Object System.Collections.Generic.List[string]  
            $f = Get-Content ("fbpmn-private/scripts/tests/config-files.json") | ConvertFrom-Json                                      
            foreach ($g in $f.psobject.properties.name) {
                if ($f."$g") { 
                    $f_bpmn.Add([string]$g) 
                }
            }
            $model
            foreach ($f in $f_bpmn) {
                $fullpath = "$env:FBPMN_HOME/models/bpmn-origin/src/$f"
                $model = (Get-ChildItem -Path $fullpath).BaseName
                fbpmn-check.ps1 $fullpath 2 *> "/tmp/$model.observed" 
                if (-NOT(F "$env:FBPMN_HOME/models/bpmn-origin/expected/$model.expected" "/tmp/$model.observed")) {
                    $r++
                } 
            }
            $r | Should -Be 0
        }
        It "V2" { 
            $r = 0
            #exécuter fbpmn-check.ps1 sur tous les modèles
            #$path = "$env:FBPMN_HOME/models/bpmn-origin/src/"   
            #$f_bpmn = Get-ChildItem -Path $path -Name -Include e00*.bpmn -Exclude eX*.bpmn
            foreach ($f in $f_bpmn) {
                $fullpath = $path + $f
                fbpmn-check $fullpath 2
            }
            #récupérer tous les fichiers json produits par fbpmn-check.ps1
            Set-Location /tmp
            #exécuter fbpmn-check sur tous les modèles
            foreach ($f in $f_bpmn) {
                $fullpath = $path + $f
                fbpmn-check.ps1 $fullpath 2
            }
            #récupérer tous les fichiers json produits par fbpmn-check
            $file_json = Get-ChildItem -Name -Include e*.json -Recurse

            $first_for_sample = Get-Content $file_json[0] | ConvertFrom-Json
            $Network = $first_for_sample.psobject.properties.name #tableau de network
            $Prop = $first_for_sample.($Network[0]).psobject.properties.name #tableau de proprieties
            #Convert from json et comparer pour chaque network et chaque prop
            for ($i = 0 ; $i -le ($file_json.Length - 1); $i++ ) {
                $from_json_ps1 = Get-Content ($file_json[$i]) | ConvertFrom-Json
                #$from_json_sh = Get-Content ($file_json_sh[$i + ($file_json.Length / 2) + 1]) | ConvertFrom-Json
                for ($j = 0 ; $j -le (($from_json_ps1.psobject.properties.name).count - 1) ; $j++ ) {
                    for ($k = 0 ; $k -le (($from_json_ps1.($Network[$j]).psobject.properties.name).count - 1) ; $k++) {
                        if (-NOT($from_json_ps1.($Network[$j]).($Prop[$k]) -eq $true )) {
                            #$from_json_sh.($Network[$j]).($Prop[$k]))) {
                            $r++ 
                        }
                    }
                }
            }
            $r | Should -Be 0
        }
    }#>
    Context "Test-Path failed" {
        It "BPMN don't exists" {
            fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/idontexist.bpmn 2  
            $LASTEXITCODE | Should -Be 1
        }
    }
}
