FROM eclipse-temurin:17.0.2_8-jre-focal

RUN apt-get update && \
    apt-get install -y --no-install-recommends libgomp1 libmpfr-dev && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

ADD lib/ lib/
ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./theta/lib/"

ADD subprojects/xsts/xsts-cli/build/libs/theta-xsts-cli-*-all.jar theta-xsts-cli.jar

ENTRYPOINT ["java", "-jar", "theta-xsts-cli.jar"]
