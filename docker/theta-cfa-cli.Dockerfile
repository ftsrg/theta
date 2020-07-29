FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y libgomp1

RUN mkdir theta
COPY . theta
RUN cd theta && \
    ./gradlew theta-cfa-cli:build && \
    cd .. && \
    mv theta/subprojects/cfa-cli/build/libs/theta-cfa-cli-*-all.jar ./theta-cfa-cli.jar

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"

ENTRYPOINT ["java", "-jar", "theta-cfa-cli.jar"]

