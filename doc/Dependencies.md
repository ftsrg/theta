# Dependencies

## Z3 Solver

The libraries for the Z3 solver are included in the _lib_ directory, both for Windows and Linux. However, on Windows, _libz3.dll_ also requires some libraries from the [Microsoft Visual C++ Redistributable package](https://www.microsoft.com/en-us/download/details.aspx?id=48145). Install it, or just execute `Download-VCredist.ps1`, which will download the required libraries.

## GraphViz

Theta can export graphs in _dot_ format and automatically convert them to images. For this, [GraphViz](http://www.graphviz.org/) has to be installed and _dot_ (or _dot.exe_ on Windows) has to be on the PATH.