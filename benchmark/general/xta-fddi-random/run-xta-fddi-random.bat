call build-xta.bat
powershell ..\Run-Measurements.ps1 -jarFile theta-xta.jar -modelsFile models-xta-fddi-random.csv -configsFile configs-xta-fddi-random.csv -timeout 60 -runs 20
call clear.bat