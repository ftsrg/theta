<#
.SYNOPSIS
Run measurements on several models and configurations with a
given number of repetitions and timeout.

.PARAMETER timeOut
Timeout in seconds. Note, that starting the JVM and the
application is also included in the time.

.PARAMETER runs
Number of repetitions for each measurement.

.PARAMETER jarFile
Path of the jar file containing the algorithm.

.PARAMETER modelsFile
CSV file describing the models.

.PARAMETER configsFile
CSV file describing the configurations.

.NOTES
Author: Akos Hajdu
#>

param (
    [int]$timeOut = 30,
    [int]$runs = 3,
    [string]$jarFile = "theta.jar",
    [Parameter(Mandatory=$true)][string]$modelsFile,
    [string]$configsFile = "configs.csv"
)

$tmpFile = [System.IO.Path]::GetTempFileName()
$logFile = "log_" + (Get-Date -format "yyyyMMdd_HHmmss") + ".csv"
# Header
"Model,Domain,Refinement,InitPrec,Search,Vars,Safe,TimeMs,Iterations,ARGsize,ARGdepth,CEXlen" | Out-File $logFile

# Load models and configurations from external files
$models = @(Import-CSV $modelsFile -Header Name, Expected)
$configs = @(Import-CSV $configsFile -Header Domain, Refinement, InitPrec, Search)

# Loop through models
$m = 0
foreach($model in $models) {
    Write-Progress -Activity "Running measurements" -PercentComplete ($m*100/$models.length) -Status "Model: $($model.Name) ($($m+1)/$($models.length))"
    
    # Loop through configurations
    $c = 0
    foreach($conf in $configs) {
        Write-Progress -Activity " " -PercentComplete ($c*100/$configs.length) -Status "Config: $conf ($($c+1)/$($configs.length))" -Id 1

        # Run each (model, configuration) pair a given times
        for($r = 0; $r -lt $runs; $r++) {
            Write-Progress -Activity " " -PercentComplete (($r)*100/$runs) -Status "Run: $($r+1)/$runs " -Id 2
            
            # Run the jar file with the given parameters, the output is redirected to a temp file
            $p = Start-Process java -ArgumentList '-jar', $jarFile, '-m', $model.Name, '-e', $model.Expected, '-d', $conf.Domain, '-r', $conf.Refinement, '-i', $conf.InitPrec, '-s', $conf.Search -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow
            $id = $p.id
            if (!$p.WaitForExit($timeOut*1000)){ # Timeout
                Stop-Process -Id $id
                Wait-Process -Id $id
                Start-Sleep -m 100 # Wait a bit so that the file is closed
                # Write timeout to the log
                ($model.Name+","+$conf.Domain+","+$conf.Refinement+","+$conf.InitPrec+","+$conf.Search+",TO") | Out-File $logFile -Append
            } else { # Normal execution
                # Copy contents of the temp file to the log
                Get-Content $tmpFile | where {$_ -ne ""} | Out-File $logFile -Append
            }
        }
        $c++
    }
    $m++
}

Remove-Item $tmpFile

Write-Progress -Activity "Running measurements" -PercentComplete 100 -Completed -Status " "