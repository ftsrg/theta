FROM eclipse-temurin:21-jre

RUN apt-get update && \
    apt-get install -y --no-install-recommends libgomp1 libmpfr-dev && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

ADD lib/ lib/
ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./lib/"

ADD subprojects/xcfa/xcfa-cli/build/libs/theta-xcfa-cli-*-all.jar /theta-xcfa-cli.jar

ENTRYPOINT ["java", "-jar", "theta-xcfa-cli.jar"]
