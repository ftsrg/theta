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

.NOTES
Author: Akos Hajdu
#>

param (
    [int]$timeOut = 30,
    [int]$runs = 3,
    [string]$jarFile = "theta.jar",
    [string]$modelsFile = "models.csv",
    [string]$configsFile = "configs.csv"
)

$tmpFile = [System.IO.Path]::GetTempFileName()
$logFile = "log_" + (Get-Date -format "yyyyMMdd_HHmmss") + ".csv"
# Header
"Model,Domain,Refinement,Initial precision,Search,Safe,Time (ms),Iterations,ARG size,ARG depth,CEX length" | Out-File $logFile

$models = Import-CSV $modelsFile -Header Name, Expected
$configs = Import-CSV $configsFile -Header Domain, Refinement, InitPrec, Search

$m = 0
foreach($model in $models) {
    Write-Progress -Activity "Running measurements" -PercentComplete ($m*100/$models.length) -Status "Model: $($model.Name) ($($m+1)/$($models.length))"
    
    $c = 0
    foreach($conf in $configs) {
        Write-Progress -Activity " " -PercentComplete ($c*100/$configs.length) -Status "Config: $conf ($($c+1)/$($configs.length))" -Id 1

        for($r = 0; $r -lt $runs; $r++) {
            Write-Progress -Activity " " -PercentComplete (($r)*100/$runs) -Status "Run: $($r+1)/$runs " -Id 2
            
            $p = Start-Process java -ArgumentList '-jar', $jarFile, '-m', $model.Name, '-e', $model.Expected, '-d', $conf.Domain, '-r', $conf.Refinement, '-i', $conf.InitPrec, '-s', $conf.Search -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow
            $id = $p.id
            if (!$p.WaitForExit($timeOut*1000)){ # Timeout
                Stop-Process -Id $id
                Wait-Process -Id $id
                Start-Sleep -m 100 # Wait a bit so that the file is closed
                ($model.Name+","+$conf[0]+","+$conf[1]+","+$conf[2]+","+$conf[3]+",TO") | Out-File $logFile -Append
            } else { # Normal execution
                Get-Content $tmpFile | where {$_ -ne ""} | Out-File $logFile -Append
            }
        }
        $c++
    }
    $m++
}

Remove-Item $tmpFile

Write-Progress -Activity "Running measurements" -PercentComplete 100 -Completed