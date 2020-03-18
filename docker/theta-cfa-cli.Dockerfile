FROM ubuntu:18.04

RUN apt-get update && \
    apt-get install -y git openjdk-11-jdk libgomp1

RUN git clone https://github.com/FTSRG/theta.git && \
    cd theta && \
    ./gradlew theta-cfa-cli:build && \
    cd ..

RUN mv theta/subprojects/cfa-cli/build/libs/theta-cfa-cli-0.0.1-SNAPSHOT-all.jar ./theta-cfa-cli.jar && \
    cp theta/lib/*.so .

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./"

ENTRYPOINT ["java", "-jar", "theta-cfa-cli.jar"]

