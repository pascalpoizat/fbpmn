BeforeAll { 
    . fbpmn-private/scripts/fbpmn-logs2dot.ps1
}

Describe 'fbpmn-logs2dot' {
    It "As much .logs as .dot" {
        Set-Location $dir
        (Get-ChildItem -Path Configs -Name -Include *.log).count -eq (Get-ChildItem -Path Configs -Name -Include *.dot).count | Should -Be True 
    }
}


