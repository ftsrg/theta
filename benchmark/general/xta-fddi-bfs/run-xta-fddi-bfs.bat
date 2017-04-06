call build-xta.bat
powershell ..\Run-Measurements.ps1 -jarFile theta-xta.jar -modelsFile models-xta-fddi-bfs.csv -configsFile configs-xta-fddi-bfs.csv -timeout 60
call clear.bat