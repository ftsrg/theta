FROM eclipse-temurin:17.0.2_8-jre-alpine

RUN apk add --no-cache libgomp mpfr-dev

ADD lib/ lib/
ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:./lib/"

ADD subprojects/xsts/xsts-cli/build/libs/theta-xsts-cli-*-all.jar theta-xsts-cli.jar

ENTRYPOINT ["java", "-jar", "theta-xsts-cli.jar"]
