FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y git libgomp1

RUN git clone https://github.com/FTSRG/theta.git && \
    cd theta && \
    ./gradlew theta-cfa-cli:build && \
    cd .. && \
    mv theta/subprojects/cfa-cli/build/libs/theta-cfa-cli-0.0.1-SNAPSHOT-all.jar ./theta-cfa-cli.jar

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"

ENTRYPOINT ["java", "-jar", "theta-cfa-cli.jar"]

