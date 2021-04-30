#!/usr/bin/env pwsh


BeforeAll { 
    . fbpmn-private/scripts/fbpmn-check.ps1

    function F {
        param ($expected, $observed)
        if ([string](Get-Content $expected | Select-Object -Skip 2) -eq [string](Get-Content $observed | Select-Object -Skip 2)) {
            #| Select-Object -Skip 3 | Select-Object -SkipLast 1)
            return $true
        } 
        return $false
    }
}



Describe 'fbpmn-check' {
    Context "Usage" {
        Context "workers" {
            It 'Good exit for wrong args.Length' {
                fbpmn-check.ps1 $FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2 3 
                $LASTEXITCODE | Should -Be 1
            } 
            It 'No args -> workers = 1' {
                fbpmn-check.ps1 $FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 
                $workers | Should -Be 1
            } 
            It 'Correct args.Length -> workers = args[1]' {
                fbpmn-check.ps1 $FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2 3 
                $workers | Should -Be 3
            } 
        }
        Context "commands java and fbpmn" {
            It 'java not found' {
                $OLD_PATH = $env:PATH
                $env:PATH = $env:PATH -replace (":/usr/bin:", ":")
                $LASTEXITCODE | Should -Be 1
                $env:PATH = $OLD_PATH
            }
            It 'fbpmn not found' {
                $OLD_PATH = $env:PATH
                $env:PATH = $env:PATH -replace (":/home/malinvaud/fbpmn-0.3.4-linux.x86_64:", ":")
                $LASTEXITCODE | Should -Be 1
                $env:PATH = $OLD_PATH 
            }
        }
        Context "env:variables" {
            It 'FBPMN_HOME not set' {
                $OLD_FBPMN_HOME = $env:FBPMN_HOME
                $env:FBPMN_HOME = ''
                $LASTEXITCODE | Should -Be 1
                $env:FBPMN_HOME = $OLD_FBPMN_HOME
            }
            It 'Wrong FBPMN_HOME' {
                $OLD_FBPMN_HOME = $env:FBPMN_HOME
                $env:FBPMN_HOME = '' #associer un directory qui n'est pas FBPMN_HOME
                $LASTEXITCODE | Should -Be 1
                $env:FBPMN_HOME = $OLD_FBPMN_HOME
            }
            It 'TLA2TOOLS_HOME not set' {
                $OLD_TLA2TOOLS_HOME = $env:TLA2TOOLS_HOME
                $env:TLA2TOOLS_HOME = ''
                $LASTEXITCODE | Should -Be 1
                $env:TLA2TOOLS_HOME = $OLD_TLA2TOOLS_HOME
            }
            It 'Wrong TLA2TOOLS_HOME ' {
                $OLD_TLA2TOOLS_HOME = $env:TLA2TOOLS_HOME
                $env:TLA2TOOLS_HOME = '' #associer un directory qui n'est pas TLA2TOOLS_HOME
                $LASTEXITCODE | Should -Be 1
                $env:TLA2TOOLS_HOME = $OLD_TLA2TOOLS_HOME
            }
        }
    }
    Context "Compare with expected" {
        It "V1" {
            $r = 0
            $f_bpmn = Get-ChildItem -Path "$env:FBPMN_HOME/models/bpmn-origin/src" -Name -Include e001*.bpmn
            #charger les fichiers dont le nom est dans le fichier de config
            $model
            foreach ($f in $f_bpmn) {
                $fullpath = "$env:FBPMN_HOME/models/bpmn-origin/src/$f"
                $model = (Get-ChildItem -Path $fullpath).BaseName
                fbpmn-check $fullpath 2 *> "/tmp/$model.observed" 
                if (-NOT(F "$env:FBPMN_HOME/models/bpmn-origin/expected/$model.expected" "/tmp/$model.observed")) {
                    $r++
                } 
            }
            $r | Should -Be 0
        }
    }
    Context "Test-Path failed" {
        It "BPMN don't exists" {
            fbpmn-check.ps1 $FBPMN_HOME/models/bpmn-origin/src/idontexist.bpmn 2  
            $LASTEXITCODE | Should -Be 1
        }
    }
}