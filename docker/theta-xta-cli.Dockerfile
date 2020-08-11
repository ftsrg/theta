FROM openjdk:11.0.6-slim

RUN apt-get update && \
    apt-get install -y libgomp1

RUN mkdir theta
COPY . theta
WORKDIR theta
RUN ./gradlew theta-xta-cli:build && \
    mv subprojects/xta-cli/build/libs/theta-xta-cli-*-all.jar ../theta-xta-cli.jar
WORKDIR ..

ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"
ENTRYPOINT ["java", "-jar", "theta-xta-cli.jar"]

