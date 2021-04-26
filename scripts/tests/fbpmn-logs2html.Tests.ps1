BeforeAll { 
    . fbpmn-private/scripts/fbpmn-logs2html.ps1
}

Describe 'fbpmn-logs2dot' {
    It "As much .logs as .html" {
        Set-Location $dir
        (Get-ChildItem -Path Configs -Name -Include *.log).count -eq (Get-ChildItem -Path Configs -Name -Include *.html).count | Should -Be True 
    }
}
