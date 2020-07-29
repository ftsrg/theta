FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y libgomp1

RUN mkdir theta
COPY . theta
RUN cd theta && \
    ./gradlew theta-sts-cli:build && \
    cd .. && \
    mv theta/subprojects/sts-cli/build/libs/theta-sts-cli-*-all.jar ./theta-sts-cli.jar

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"

ENTRYPOINT ["java", "-jar", "theta-sts-cli.jar"]
