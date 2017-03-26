# Benchmarking

## Running measurements
- Requirements
  - Windows OS
  - JRE 8
  - PowerShell (usually part of Windows)
- Execute `build.bat` from the command line, a jar file and some dlls should appear
- Execute `Run-Measurements.ps1` from PowerShell
  - Type `Get-Help .\Run-Measurements.ps1 -detailed` to get help about the parameters of the script
  - Configurations are listed in the file `configs.csv`
  - Models are listed in the files `models-XXX.csv`
  - Example: `.\Run-Measurements.ps1 -configsFile .\configs.csv -modelsFile .\models-simple.csv -runs 1 -timeOut 15`
- Sit back and enjoy the nice progress bars
- Observe the results in the generated csv file, which is named `log_<timestamp>.csv` by default

## Extras

### Generate html report
- Requirements
  - [R](https://www.r-project.org/) with the [tidyverse](https://cran.r-project.org/web/packages/tidyverse/index.html) package installed
  - [RStudio Desktop](https://www.rstudio.com/products/RStudio/)
  - [Pandoc](http://pandoc.org/)
- When executing `Run-Measurements.ps1`, supply the _bin_ folder of R (e.g., _C:\Program Files\R\R-3.3.2\bin_) to the `-rBin` parameter.
- A html report (with the same name as the log file) should appear.

### Send results in e-mail
If you want to send the results by e-mail when the script is done, add the following line to the very end of the script (and fill the arguments): `Send-MailMessage -to "..." -from "..." -Subject "Benchmark finished" -SmtpServer "..." -Attachments $logFile`.
-
