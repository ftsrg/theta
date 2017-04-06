call build-xta.bat
powershell ..\Run-Measurements.ps1 -jarFile theta-xta.jar -modelsFiles models-xta-bfs.csv -configsFile configs-xta-bfs.csv -timeOut 60 -runs 1
call clear.bat