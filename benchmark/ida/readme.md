# IDA Home Assignment
This directory contains measurements and analysis for the Intelligent Data Analysis course home assignment.

## Build
* Run `build.bat` to build the project.
* The main jar file and dependency dlls will be copied into the root directory.

## Run measurements
* Run the PowerShell command `.\Run-Measurements.ps1 -modelsFile ./models.csv -configsFile ./configs.csv -runs 5 -timeOut 480 -outDir ./results/`
* The results will appear in a csv file under the _results_ directory.
  * Our result file is also included in this directory.

## Analyze data
* The data analysis script `report.Rmd` can be found under the _results_ directory.
  * The script is a so-called R markdown file, which is a markdown file with R code snippets inserted.
  * From this script a pdf or a html file can be generated using R (3.3.2) and RStudio (1.0.44). During generation, the code snippets are evaluated and the results (e.g., plots are rendered in the final document).
  * The path of the csv file is contained in a variable in the script.
* Our result pdf and html is also included in the _results_ directory.