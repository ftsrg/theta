# IDA Home Assignment
This directory contains measurements and analysis for the Intelligent Data Analysis course home assignment.

## Run measurements
* Build the project with the `Main` class in the `hu.bme.mit.theta.frontend.benchmark` project. Put the resulting `theta.jar` into the root directory.
* Copy the Z3 related dlls into the root directory.
* Run the PowerShell command `.\Run-Measurements.ps1 -modelsFile ./models.csv -configsFile ./configs.csv -runs 5 -timeOut 480 -outDir ./results/`
* The results will appear in a csv file under the _results_ directory.
