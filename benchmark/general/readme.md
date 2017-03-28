# Benchmarking

## Running measurements
1. Requirements
    - Windows OS
    - JRE 8
    - PowerShell (usually part of Windows)
1. Execute `build-XXX.bat` from the command line to build a certain version of the tool (for example, `build-sts.bat` for the STS formalism). A jar file and some dlls should appear.
1. Execute `Run-Measurements.ps1` from PowerShell
    - Type `Get-Help .\Run-Measurements.ps1 -detailed` to get help about the parameters of the script
    - Configurations are listed in the files `configs-XXX.csv`
    - Models are listed in the files `models-XXX.csv`
    - Example: `.\Run-Measurements.ps1 -jarFile theta-sts.jar -configsFile .\configs-sts.csv -modelsFile .\models-sts-simple.csv -runs 1 -timeOut 15`
1. Sit back and enjoy the nice progress bars
1. Observe the results in the generated csv file, which is named `log_<timestamp>.csv` by default

## Extras

### Generate html report
1. Requirements
    - **Currently only for theta-sts!**
    - [R](https://www.r-project.org/) with the [tidyverse](https://cran.r-project.org/web/packages/tidyverse/index.html) package installed
    - [RStudio Desktop](https://www.rstudio.com/products/RStudio/)
    - [Pandoc](http://pandoc.org/)
1. When executing `Run-Measurements.ps1`, supply the _bin_ folder of R (e.g., _C:\Program Files\R\R-3.3.2\bin_) to the `-rBin` parameter.
1. A html report (with the same name as the log file) should appear.

### Send results in e-mail
If you want to send the results by e-mail when the script is done, add the following line to the very end of the script (and fill the arguments): `Send-MailMessage -to "..." -from "..." -Subject "Benchmark finished" -SmtpServer "..." -Attachments $logFile`.
