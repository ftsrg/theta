$z3release = "z3-4.5.0"
$z3version = "z3-4.5.0-x64-win"

$currentPath = (Resolve-Path .\).Path

[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12

$clnt = new-object System.Net.WebClient
$url = "https://github.com/Z3Prover/z3/releases/download/$z3release/$z3version.zip"
$zipFilePath = "$currentPath\$z3version.zip"
$clnt.DownloadFile($url, $zipFilePath)

$shellApp = new-object -com shell.application 
$zipFile = $shellApp.namespace($zipFilePath)
$dest = $shellApp.namespace($currentPath) 
$dest.Copyhere($zipFile.items())

Copy-Item "$currentPath\$z3version\bin\msvcp110.dll" -Destination $currentPath
Copy-Item "$currentPath\$z3version\bin\msvcr110.dll" -Destination $currentPath
Copy-Item "$currentPath\$z3version\bin\vcomp110.dll" -Destination $currentPath

Remove-Item $zipFilePath
Remove-Item "$currentPath\$z3version" -Recurse
