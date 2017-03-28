<#
.SYNOPSIS
Run measurements on several models and configurations with a given number of
repetitions and timeout. The script collects the output from the standard
output to a csv file.

.PARAMETER jarFile
Path of the jar file containing the algorithm.

.PARAMETER modelsFile
A list of csv files listing the models.

.PARAMETER configsFile
Csv file listing the configurations.

.PARAMETER timeOut
Timeout in seconds. Note, that starting the JVM and the
application is also included in the time.

.PARAMETER runs
Number of repetitions for each measurement.

.PARAMETER toNoRep
Do not repeat a measurement if it causes a timeout on its first run.

.PARAMETER rBin
Path to the binary folder of the R statistical framework. If this parameter
and rReport is given, the script will also generate a html report.

.PARAMETER rReport
Path to the R markdown file that is used for generating the report. If this
parameter and rBin is given, the script will also generate a html report.

.NOTES
Author: Akos Hajdu
#>

param (
    [Parameter(Mandatory=$true)][string]$jarFile,
    [Parameter(Mandatory=$true)][string[]]$modelsFile,
    [Parameter(Mandatory=$true)][string]$configsFile,
    [int]$timeOut = 60,
    [int]$runs = 1,
    [switch]$toNoRep,
    [string]$rBin,
    [string]$rReport
)

# Temp file for individual runs
$tmpFile = [System.IO.Path]::GetTempFileName()
# Final log file collecting results from all runs
# (The temp file is needed because I could not redirect the output of the application to a file
#  in append mode. Therefore, the temp file is always overwritten, but the script always appends
#  the contents of the temp file to the final log file.)
$logFile = "log_" + (Get-Date -format "yyyyMMdd_HHmmss") + ".csv"
# Header
(Start-Process java -ArgumentList @('-jar', $jarFile, '--header') -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow).WaitForExit()
Get-Content $tmpFile | where {$_ -ne ""} | Out-File $logFile

# Load models and configurations from external files
$models = @(Import-CSV $modelsFile)
$modelsOpts = $models[0] # First line should be the name of the options
$models = $models | select -Skip 1 # Other lines are data

$configs = @(Import-CSV $configsFile)
$configsOpts = $configs[0] # First line should be the name of the options
$configs = $configs | select -Skip 1 # Other lines are data

# Loop through models
$m = 0
foreach($model in $models) {
    Write-Progress -Activity "Running measurements" -PercentComplete ($m*100/$models.length) -Status "Model: $($model) ($($m+1)/$($models.length))"
    
    # Loop through configurations
    $c = 0
    foreach($conf in $configs) {
        Write-Progress -Activity " " -PercentComplete ($c*100/$configs.length) -Status "Config: $conf ($($c+1)/$($configs.length))" -Id 1

        # Run each (model, configuration) pair a given times
        for($r = 0; $r -lt $runs; $r++) {
            Write-Progress -Activity " " -PercentComplete (($r)*100/$runs) -Status "Run: $($r+1)/$runs " -Id 2
            
            # Collect arguments for the jar file
            $args = @('-jar', $jarFile)
            # Arguments from the configuration
            foreach ($arg in $conf | Get-Member -MemberType 'NoteProperty' | Select-Object -ExpandProperty 'Name') {
                if ($conf.$arg) { $args += @($configsOpts.$arg, $conf.$arg) }
            }
            # Arguments from the model
            foreach ($arg in $model | Get-Member -MemberType 'NoteProperty' | Select-Object -ExpandProperty 'Name') {
                if ($model.$arg) { $args += @($modelsOpts.$arg, $model.$arg) }
            }
            # Run the jar file with the given parameters, the output is redirected to a temp file
            $p = Start-Process java -ArgumentList $args -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow
            $id = $p.id
            if (!$p.WaitForExit($timeOut*1000)){ # Timeout
                Stop-Process -Id $id
                Wait-Process -Id $id
                Start-Sleep -m 100 # Wait a bit so that the file is closed
                if ($r -eq 0 -and $toNoRep) { $r = $runs } # Do not repeat if the first run is a timeout
            } 
            # Copy contents of the temp file to the log
            Get-Content $tmpFile | where {$_ -ne ""} | Out-File $logFile -Append
        }
        $c++
    }
    $m++
}

Remove-Item $tmpFile

# Convert to UTF-8
$contents = Get-Content $logFile
[System.IO.File]::WriteAllLines((Get-ChildItem $logFile).FullName, $contents)

Write-Progress -Activity "Running measurements" -PercentComplete 100 -Completed -Status " "

# Generate report
if ($rBin -and $rReport) {
    $params = @("-e", "`"rmarkdown::render('$rReport', params = list(csv_path = '$logFile', timeout_ms = $($timeOut * 1000)))`"")
    $p = Start-Process "$rBin\Rscript.exe" -ArgumentList $params -PassThru -NoNewWindow
    $p.WaitForExit()
    Rename-Item $rReport.replace(".Rmd", ".html") ($logFile.replace(".csv", "") + ".html")
}