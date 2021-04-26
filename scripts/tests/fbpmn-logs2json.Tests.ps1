BeforeAll { 
    . fbpmn-private/scripts/fbpmn-logs2json.ps1
}

Describe 'fbpmn-logs2json' {
    It "As much .logs as .json" {
        Set-Location $dir
        (Get-ChildItem -Path Configs -Name -Include *.log).count -eq (Get-ChildItem -Path Configs -Name -Include *.json).count | Should -Be True 
    }
}

