BeforeAll { 
    . fbpmn-private/scripts/fbpmn-check.ps1
}

Describe 'fbpmn-check' {
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

        }
        It 'fbpmn not found' {
            
        }
    }
    Context "env:variables" {
        It 'FBPMN_HOME not set' {
            $OLD_FBPMN_CODE = $env:FBPMN_HOME
            $env:FBPMN_HOME = ''
            $LASTEXITCODE | Should -Be 1
            $env:FBPMN_HOME = $OLD_FBPMN_CODE
        }
        It 'Wrong FBPMN_HOME' {
            $OLD_FBPMN_CODE = $env:FBPMN_HOME
            $env:FBPMN_HOME = '' #associer un directory qui n'est pas FBPMN_HOME
            $LASTEXITCODE | Should -Be 1
            $env:FBPMN_HOME = $OLD_FBPMN_CODE
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
    Context "mktemp" {
        It "mdir create" {
            $dir = New-Dir $FBPMN_HOME/models/bpmn-origin/src/e033MBE.bpmn e033MBE
            [string](Get-ChildItem -Path /tmp -Filter e033MBE.*) -eq [string]$dir | Should -Be True
            Remove-Item $dir
        }
    }
    Context "Test-Path failed" {
        It "BPMN don't exists" {
            fbpmn-check.ps1 $FBPMN_HOME/models/bpmn-origin/src/idontexist.bpmn 2  
            $LASTEXITCODE | Should -Be 1
        }
        It "TransfoRemove-Itemation failed" {

        }
    }
    Context "Compare Directory" {
        
    }
    Context "Writing good" {
        It "StatsBPMN.tla" {

        }
        It "model.constraint" {
            
        }
    }
}