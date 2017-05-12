call build-xta.bat
powershell ..\Run-Measurements.ps1 -jarFile theta-xta.jar -modelsFile models-xta-fddi-dfs.csv -configsFile configs-xta-fddi-dfs.csv -timeout 60
call clear.bat