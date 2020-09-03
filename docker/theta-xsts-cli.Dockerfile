FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y --no-install-recommends libgomp1 && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

RUN mkdir theta
COPY . theta
WORKDIR /theta
RUN ./gradlew clean && \
    ./gradlew theta-xsts-cli:build && \
    mv subprojects/xsts-cli/build/libs/theta-xsts-cli-*-all.jar /theta-xsts-cli.jar
WORKDIR /

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"
ENTRYPOINT ["java", "-jar", "theta-xsts-cli.jar"]
