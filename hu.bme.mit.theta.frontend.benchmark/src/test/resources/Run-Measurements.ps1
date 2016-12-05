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
    [string]$jarFile = "theta.jar"
)

$tmpFile = [System.IO.Path]::GetTempFileName();
$logFile = "log_" + (Get-Date -format "yyyyMMdd_HHmmss") + ".txt";


# List of models: path and expected output
$models = @(
    #@("hw/srg5ptimonegnv.aag", $False),
    @("simple/boolean1.system", $False),
    @("simple/boolean2.system", $False),
    @("simple/counter.system", $True),
    @("simple/counter_bad.system", $False),
	@("simple/counter_parametric.system", $True),
	@("simple/loop.system", $True),
	@("simple/loop_bad.system", $False),
	@("simple/multipleinitial.system", $False),
	@("simple/readerswriters.system", $True),
	@("simple/simple1.system", $False),
	@("simple/simple2.system", $True),
	@("simple/simple3.system", $False)
);

# List of configurations: domain, refinement, init. prec., search
$configs = @(
	@("PRED", "CRAIG_ITP", "EMPTY", "BFS"),
	@("PRED", "CRAIG_ITP", "EMPTY", "DFS"),
	@("PRED", "CRAIG_ITP", "PROP", "BFS"),
	@("PRED", "CRAIG_ITP", "PROP", "DFS"),
	@("PRED", "SEQ_ITP", "EMPTY", "BFS"),
	@("PRED", "SEQ_ITP", "EMPTY", "DFS"),
	@("PRED", "SEQ_ITP", "PROP", "BFS"),
	@("PRED", "SEQ_ITP", "PROP", "DFS"),
	@("EXPL", "CRAIG_ITP", "EMPTY", "BFS"),
	@("EXPL", "CRAIG_ITP", "EMPTY", "DFS"),
	@("EXPL", "CRAIG_ITP", "PROP", "BFS"),
	@("EXPL", "CRAIG_ITP", "PROP", "DFS"),
	@("EXPL", "SEQ_ITP", "EMPTY", "BFS"),
	@("EXPL", "SEQ_ITP", "EMPTY", "DFS"),
	@("EXPL", "SEQ_ITP", "PROP", "BFS"),
	@("EXPL", "SEQ_ITP", "PROP", "DFS"),
	@("EXPL", "UNSAT_CORE", "EMPTY", "BFS"),
	@("EXPL", "UNSAT_CORE", "EMPTY", "DFS"),
	@("EXPL", "UNSAT_CORE", "PROP", "BFS"),
	@("EXPL", "UNSAT_CORE", "PROP", "DFS")
);

$m = 0
foreach($model in $models) {
    Write-Progress -Activity "Running measurements" -PercentComplete ($m*100/$models.length) -Status "Model: $($model[0]) ($($m+1)/$($models.length))"
    
    $c = 0
    foreach($conf in $configs) {
        Write-Progress -Activity " " -PercentComplete ($c*100/$configs.length) -Status "Config: $conf ($($c+1)/$($configs.length))" -Id 1

        for($r = 0; $r -lt $runs; $r++) {
            Write-Progress -Activity " " -PercentComplete (($r)*100/$runs) -Status "Run: $($r+1)/$runs " -Id 2
            
            $p = Start-Process java -ArgumentList '-jar', $jarFile, '-m', $model[0], '-e', $model[1], '-d', $conf[0], '-r', $conf[1], '-i', $conf[2], '-s', $conf[3] -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow
            $id = $p.id
            if (!$p.WaitForExit($timeOut*1000)){ # Timeout
                Stop-Process -Id $id
                Wait-Process -Id $id
                Start-Sleep -m 100 # Wait a bit so that the file is closed
                ($model[0]+";"+$conf[0]+";"+$conf[1]+";"+$conf[2]+";"+$conf[3]+";TO") | Out-File $logFile -Append
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