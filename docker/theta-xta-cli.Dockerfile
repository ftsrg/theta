FROM eclipse-temurin:21-jre

RUN apt-get update && \
    apt-get install -y --no-install-recommends libgomp1 libmpfr-dev && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

ADD lib/ lib/
ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./lib/"

ADD subprojects/xta/xta-cli/build/libs/theta-xta-cli-*-all.jar /theta-xta-cli.jar

ENTRYPOINT ["java", "-jar", "theta-xta-cli.jar"]
