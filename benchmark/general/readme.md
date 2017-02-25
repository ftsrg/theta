Run measurements
* Requrements: Windows OS, JRE 8, PowerShell (usually part of Windows)
* Execute `build.bat` from the command line (no arguments needed)
  * A jar file and some dlls should appear
* Execute `Run-Measurements.ps1` from PowerShell
  * Type `Get-Help .\Run-Measurements.ps1 -detailed` to get help about the parameters of the script
  * Configurations are listed in the file `configs.csv`
  * Models are listed in the files `models-XXX.csv` 
  * Example: `.\Run-Measurements.ps1 -configsFile .\configs.csv -modelsFile .\models-simple.csv -runs 1 -timeOut 15`
* Sit back and enjoy the nice progress bars
* Observe the results in the generated csv file (which is named `log_XXX.csv` by default)