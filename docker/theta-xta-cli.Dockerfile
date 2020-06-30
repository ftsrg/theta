FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y git libgomp1

RUN git clone https://github.com/FTSRG/theta.git && \
    cd theta && \
    ./gradlew theta-xta-cli:build && \
    cd .. && \
    mv theta/subprojects/xta-cli/build/libs/theta-xta-cli-*-all.jar ./theta-xta-cli.jar

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"

ENTRYPOINT ["java", "-jar", "theta-xta-cli.jar"]

