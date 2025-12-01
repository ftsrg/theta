FROM eclipse-temurin:17.0.2_8-jre-focal

RUN apt-get update && \
    apt-get install -y --no-install-recommends libgomp1 libmpfr-dev && \
    apt-get clean && rm -rf /var/lib/apt/lists/*

ADD lib/ lib/
ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./lib/"

ADD subprojects/cfa/cfa-cli/build/libs/theta-cfa-cli-*-all.jar /theta-cfa-cli.jar

ENTRYPOINT ["java", "-jar", "/theta-cfa-cli.jar"]
