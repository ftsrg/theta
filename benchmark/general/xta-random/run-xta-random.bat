call build-xta.bat
powershell ..\Run-Measurements.ps1 -jarFile theta-xta.jar -modelsFiles models-xta-random.csv -configsFile configs-xta-random.csv -timeOut 30 -runs 10
call clear.bat