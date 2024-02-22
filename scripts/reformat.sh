#!/bin/bash
scriptdir=$(dirname $(realpath "$0"))

docker run -v $scriptdir/..:/github/workspace ghcr.io/leventebajczi/intellij-format:latest '*java,*kts,*kt' "" ./doc/ThetaIntelliJCodeStyle.xml

