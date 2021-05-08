#!/usr/bin/env pwsh


BeforeAll { 
    . fbpmn-private/scripts/fbpmn-check.ps1
    function Replace {
        param($path)
        $OLD_PATH = $env:PATH
        $env:PATH = $env:PATH -replace ($path, ":")
        fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 2
        $LASTEXITCODE | Should -Be 1
        $env:PATH = $OLD_PATH
    }
    function Write-Logs {
        param($i, $j, $k)
        Write-Host $model $json_expected.$model.($Network[$i]).($Prop[$j]).value
        Write-Host $Network[$i] . $Prop[$j]
        Write-Host "observed:" $json_observed.$model.($Network[$i]).($Prop[$j])
        Write-Host "expected:" $json_expected.$model.($Network[$i]).($Prop[$j])
        Write-Host ""
    }
    function Compare-JSON {
        param ($model, $expected, $observed, $strong = $false)
        $json_expected = Get-Content $expected | ConvertFrom-Json
        $Network = $json_expected.$model.psobject.properties.name 
        $Prop = $json_expected.$model.($Network[0]).psobject.properties.name 
        $Result = $json_expected.$model.($Network[0]).($Prop[0]).psobject.properties.name
        $json_observed = Get-Content $observed | ConvertFrom-Json
        
        for ($i = 0 ; $i -le (($json_expected.$model.psobject.properties.name).count - 1) ; $i++ ) {
            #for every network
            for ($j = 0 ; $j -le (($json_expected.$model.($Network[$i]).psobject.properties.name).count - 1) ; $j++) {
                #for every props
                if ($json_observed.$model.($Network[$i]).($Prop[$j]).value -eq $json_expected.$model.($Network[$i]).($Prop[$j]).value) {
                    # prop full or not for both instances
                    if ($json_observed.$model.($Network[$i]).($Prop[$j]).value -eq $true) {
                        #égalité parfaite quand Prop est remplie
                        for ($k = 0 ; $k -le (($json_expected.$model.($Network[$i]).($Prop[$j]).psobject.properties.name).count - 1) ; $k++) {
                            if (-NOT($json_observed.$model.($Network[$i]).($Prop[$j]).($Result[$k]) -eq $json_expected.$model.($Network[$i]).($Prop[$j]).($Result[$k]))) {
                                Write-Logs $i $j $k 
                                if ($strong) {
                                    return $false
                                }
                            }
                        }
                    }
                    else {
                        #égalité partielle quand Prop n'est pas remplie
                        if ((-NOT($json_observed.$model.($Network[$i]).($Prop[$j]).trans -eq $json_expected.$model.($Network[$i]).($Prop[$j]).trans)) -or (-NOT($json_observed.$model.($Network[$i]).($Prop[$j]).states -eq $json_expected.$model.($Network[$i]).($Prop[$j]).states))) {
                            Write-Logs $i $j $k  
                        }
                    }
                }
                else {
                    return $false
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
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 2 3 
                $LASTEXITCODE | Should -Be 1
            } 
            It 'No args -> workers = 1' {
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 1 *> /tmp/e001ClientSupplier.out
                $a = Select-String "Working in" -Path /tmp/e001ClientSupplier.out -NoEmphasis 
                $a -match "with (\d)"
                $matches[1] | Should -Be 1
            } 
            It 'Correct args.Length -> workers = args[1]' {
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 3 *> /tmp/e001ClientSupplier.out
                $a = Select-String "Working in" -Path /tmp/e001ClientSupplier.out -NoEmphasis 
                $a -match "with (\d)"
                $matches[1] | Should -Be 3 
            } 
        }
        Context "commands java and fbpmn" {
            It 'java not found' {
                Replace ":/usr/bin:"
            }
            It 'fbpmn not found' {
                Replace ":/home/malinvaud/fbpmn-0.3.4-linux.x86_64:"
            }
        }
        Context "env:variables" {
            BeforeEach {
                $OLD_FBPMN_HOME = $env:FBPMN_HOME
                $OLD_TLA2TOOLS_HOME = $env:TLA2TOOLS_HOME
            }
            It 'FBPMN_HOME not set' {
                $env:FBPMN_HOME = ''
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 2
                $LASTEXITCODE | Should -Be 1
            }
            It 'Wrong FBPMN_HOME' {
                $dir = New-Item -ItemType Directory -Path /home/malinvaud/temp1
                $env:FBPMN_HOME = $dir
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 2
                $LASTEXITCODE | Should -Be 1
                Remove-Item -Path $dir 
            }
            It 'TLA2TOOLS_HOME not set' {
                $env:TLA2TOOLS_HOME = ''
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 2
                $LASTEXITCODE | Should -Be 1
            }
            It 'Wrong TLA2TOOLS_HOME ' {
                $dir = New-Item -ItemType Directory -Path /home/malinvaud/temp2 
                $env:TLA2TOOLS_HOME = $dir
                fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/e001ClientSupplier.bpmn 2
                $LASTEXITCODE | Should -Be 1
                Remove-Item -Path $dir 
            }
            AfterEach {
                $env:FBPMN_HOME = $OLD_FBPMN_HOME
                $env:TLA2TOOLS_HOME = $OLD_TLA2TOOLS_HOME
            }
        }
    }
    Context "Compare observed with expected" {
        It "Differentiated JSON tests" { 
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
                fbpmn-check.ps1 $fullpath *> $null
                if (-NOT(Compare-JSON $model "$env:FBPMN_HOME/models/bpmn-origin/expected/$model.json" "$model.json" $true)) {
                    $r++                    
                } 
            }
            $r | Should -Be 0
        }
    }
    Context "Test-Path failed" {
        It "BPMN don't exists" {
            fbpmn-check.ps1 $env:FBPMN_HOME/models/bpmn-origin/src/dontexist.bpmn 2  
            $LASTEXITCODE | Should -Be 1
        }
    }
}

AfterAll {
    Set-Location ..
    Get-ChildItem /tmp -Filter e0*.* | Remove-Item -Recurse 
}

