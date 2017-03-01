pushd "../../"
call gradlew.bat stsMain
popd
copy "..\..\hu.bme.mit.theta.frontend.benchmark\build\libs\hu.bme.mit.theta.frontend.benchmark-1.0.0-SNAPSHOT-fat.jar" "theta.jar" /Y
copy "..\..\lib\*.dll" "*.dll"