# IDA Home Assignment
This directory contains measurements and analysis for the Intelligent Data Analysis course home assignment.

## Build
* Run `build.bat` to build the project.
* The main jar file and dependency dlls will be copied into the root directory.

## Run measurements
* Run the PowerShell command `.\Run-Measurements.ps1 -modelsFile ./models.csv -configsFile ./configs.csv -runs 5 -timeOut 480 -outDir ./results/`
* The results will appear in a csv file under the _results_ directory.

## Analyze data
* Install packages `ggplot2`, `iplots`m `dplyr`, `party`.
  * This can be done for example in RStudio: Packages tab -> Install.