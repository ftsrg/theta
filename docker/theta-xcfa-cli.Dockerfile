FROM ubuntu:24.04

RUN apt-get update && \
    apt-get install -y --no-install-recommends openjdk-17-jre-headless libgomp1 libmpfr-dev && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

RUN mkdir theta
COPY . theta
WORKDIR /theta
RUN ./gradlew clean && \
    ./gradlew theta-xcfa-cli:build && \
    mv subprojects/xcfa/xcfa-cli/build/libs/theta-xcfa-cli-*-all.jar /theta-xcfa-cli.jar
WORKDIR /

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"
ENTRYPOINT ["java", "-jar", "theta-xcfa-cli.jar"]
