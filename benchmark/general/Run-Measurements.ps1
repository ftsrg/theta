<#
.SYNOPSIS
Run an algorithm (given in a jar file) on several models and configurations
(listed in csv files), with a given number of repetitions and timeout. The
script collects the input parameters and the output of the algorithm into
a csv file. Optionally a html report can be generated using the R framework.

.PARAMETER jarFile
Path of the jar file containing the algorithm. The jar file must print its
output in csv format, and must print a header when called with a single
'--header' flag.

.PARAMETER modelsFiles
A list of csv files listing the models. The first row must contain the names
of the parameters and the second row must contain the switches.

.PARAMETER configsFile
Csv file listing the configurations. The first row must contain the names
of the parameters and the second row must contain the switches.

.PARAMETER timeOut
Timeout in seconds. Note, that starting the JVM and the application is also
included in the time.

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

.PARAMETER transform
Path to a script that transforms the csv. This transformation is executed
before generating the report. The original file is also kept. The script
must accept two parameters '-logFileIn' and '-logFileOut'.

.PARAMETER jvmArgs
A list of additional arguments to pass to the JVM.

.NOTES
Author: Akos Hajdu
#>

param (
    [Parameter(Mandatory=$true)][string]$jarFile,
    [Parameter(Mandatory=$true)][string[]]$modelsFiles,
    [Parameter(Mandatory=$true)][string]$configsFile,
    [int]$timeOut = 60,
    [int]$runs = 1,
    [switch]$toNoRep,
    [string]$rBin,
    [string]$rReport,
    [string[]]$transform,
    [string[]]$jvmArgs = @()
)

function MemberNames
{
    $args[0] | Get-Member -MemberType 'NoteProperty' | Select-Object -ExpandProperty 'Name' | Sort-Object
}

# Temp file for individual runs
$tmpFile = [System.IO.Path]::GetTempFileName()
# Final log file collecting results from all runs
# (The temp file is needed because I could not redirect the output of the application to a file
#  in append mode. Therefore, the temp file is always overwritten, but the script always appends
#  the contents of the temp file to the final log file.)
$logFile = "log_" + (Get-Date -format "yyyyMMdd_HHmmss") + ".csv"

# Load models
$models = @()
foreach ($file in $modelsFiles) {
    $content = @(Import-CSV $file)
    $modelsOpts = $content[0] # First line should be the names of the options
    $models += @($content | select -Skip 1) # Other lines are data
}
# Load configurations
$configs = @(Import-CSV $configsFile)
$configsOpts = $configs[0] # First line should be the names of the options
$configs = @($configs | select -Skip 1) # Other lines are data

# Header
$header = ""
foreach ($arg in MemberNames $modelsOpts) { $header += "`"$arg`"," }
foreach ($arg in MemberNames $configsOpts) { $header += "`"$arg`"," }
(Start-Process java -ArgumentList @('-jar', $jarFile, '--header') -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow).WaitForExit()
$header += Get-Content $tmpFile | where {$_ -ne ""}
$header | Out-File $logFile

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
            
            $output = ""
            # Collect arguments for the jar file
            $args = @($jvmArgs) + @('-jar', $jarFile)
            # Arguments from the model
            foreach ($arg in MemberNames $modelsOpts) {
                if ($model.$arg) { $args += @($modelsOpts.$arg, $model.$arg) }
                $output += "`"$($model.$arg)`","
            }
            # Arguments from the configuration
            foreach ($arg in MemberNames $configsOpts) {
                if ($conf.$arg) { $args += @($configsOpts.$arg, $conf.$arg) }
                $output += "`"$($conf.$arg)`","
            }
            # Run the jar file with the given parameters, the output is redirected to a temp file
            $p = Start-Process java -ArgumentList $args -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow
            $id = $p.id
            if (!$p.WaitForExit($timeOut*1000)){ # Timeout
                Stop-Process -Id $id
                Wait-Process -Id $id
                Start-Sleep -m 100 # Wait a bit so that the file is closed
                if ($r -eq 0 -and $toNoRep) { $r = $runs } # Do not repeat if the first run is a timeout
                $output += "`"[TO]`""
            } else {
                $output += Get-Content $tmpFile | where {$_ -ne ""}
            }
            # Copy contents of the temp file to the log
            $output | Out-File $logFile -Append
        }
        $c++
    }
    $m++
}

Remove-Item $tmpFile

$logFile_t = $logFile
if($transform) {
    $logFile_t = $logFile.Replace(".csv", "_transf.csv")
    $params = @("-logFileIn", $logFile, "-logFileOut", $logFile_t)
    Invoke-Expression "$transform $params"
}

# Convert to UTF-8
$contents = Get-Content $logFile_t
[System.IO.File]::WriteAllLines((Get-ChildItem $logFile_t).FullName, $contents)

Write-Progress -Activity "Running measurements" -PercentComplete 100 -Completed -Status " "

# Generate report
if ($rBin -and $rReport) {
    $params = @("-e", "`"rmarkdown::render('$rReport', params = list(csv_path = '$logFile_t', timeout_ms = $($timeOut * 1000)))`"")
    (Start-Process "$rBin\Rscript.exe" -ArgumentList $params -PassThru -NoNewWindow).WaitForExit()
    Rename-Item $rReport.replace(".Rmd", ".html") ($logFile_t.replace(".csv", "") + ".html")
}