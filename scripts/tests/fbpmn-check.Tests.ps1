BeforeAll { 
    . fbpmn-private/scripts/fbpmn-check.ps1
}

Describe 'fbpmn-check' {
    Context "Usage" {
        Context "workers" {
            It 'Good exit for wrong args.Length' {
                fbpmn-check.ps1 $FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn 2 3 
                $LASTEXITCODE | Should -Be 1
            } 
            It 'No args -> workers = 1' {
                Get-Worker | Should -Be 1
            } 
            It 'Correct args.Length -> workers = args[1]' {
                Get-Worker 2 3 | Should -Be 3
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
    Context "TLA généré" {
        It "TLA généré" { 'pour chaque f dans $FBPMN_HOME/models/src/bpmn_origin/x_f.bpmn'
            $r = 0    
            $path = "$env:FBPMN_HOME/models/bpmn-origin/src/"   
            $f_bpmn = Get-ChildItem -Path $path -Name -Include e*.bpmn -Exclude eX*.bpmn
            foreach ($f in $f_bpmn) {
                $fullpath = $path + $f
                fbpmn-check.ps1 $fullpath 2
            }
            Set-Location .. 
            $f_temp = Get-ChildItem -Name -Include e*.tla -Recurse
            $f_tla = Get-ChildItem -Path $env:FBPMN_HOME/models/bpmn-origin/tla_from_bpmn -Name -Include e*.tla -Exclude eX*.tla
            
            for ($i = 0 ; $i -le ($f_tla.Length - 1); $i++ ) {
                $name = $f_tla[$i]
                if ([string](Get-Content $f_temp[$i]) -ne [string](Get-Content "$env:FBPMN_HOME/models/bpmn-origin/tla_from_bpmn/$name")) { $r++ } 
            }
            $r | Should -Be 0
            Remove-Item e*.* -Recurse -Force
        } 
    }
    Context "Proprieties" {
        
    }
    Context "Test-Path failed" {
        It "BPMN don't exists" {
            fbpmn-check.ps1 $FBPMN_HOME/models/bpmn-origin/src/idontexist.bpmn 2  
            $LASTEXITCODE | Should -Be 1
        }
        It "bpmn2tla" {

        }
    }
}