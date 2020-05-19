FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y git libgomp1

RUN git clone https://github.com/mondokm/theta.git && \
    cd theta && \
    git checkout xsts && \
    ./gradlew theta-xsts-cli:build && \
    cd .. && \
    mv theta/subprojects/xsts-cli/build/libs/theta-xsts-cli-0.0.1-SNAPSHOT-all.jar ./theta-xsts-cli.jar

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"

ENTRYPOINT ["java", "-jar", "theta-xsts-cli.jar"]

