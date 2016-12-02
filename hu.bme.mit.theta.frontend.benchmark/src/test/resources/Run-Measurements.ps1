$timeOutMs = 30000;
$runs = 3;
$tmpFile = [System.IO.Path]::GetTempFileName();
$logFile = "log_" + (Get-Date -format "yyyyMMdd_HHmmss") + ".txt";
$jarFile = "theta.jar"

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

foreach($model in $models) {
    Write-Host ("Model: " + $model[0])
    foreach($conf in $configs) {
        Write-Host ("`tConfig: " + $conf) -NoNewLine
        for($r = 1; $r -le $runs; $r++) {
            Write-Host (" " + $r) -NoNewLine
            $p = Start-Process java -ArgumentList '-jar', $jarFile, '-m', $model[0], '-d', $conf[0], '-r', $conf[1], '-i', $conf[2], '-s', $conf[3] -RedirectStandardOutput $tmpFile -PassThru -NoNewWindow
            $id = $p.id
            if (!$p.WaitForExit($timeOutMs)){
                Stop-Process -Id $id
                Wait-Process -Id $id
                Start-Sleep -m 100
                ($model[0]+";"+$conf[0]+";"+$conf[1]+";"+$conf[2]+";"+$conf[3]+";TO") | Out-File $logFile -Append
            } else {
                Get-Content $tmpFile | where {$_ -ne ""} | Out-File $logFile -Append
            }
        }
        Write-Host ""
    }
}

Remove-Item $tmpFile

