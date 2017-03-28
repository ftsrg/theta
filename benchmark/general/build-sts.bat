pushd "../../"
call gradlew.bat stsMain
popd
copy "..\..\hu.bme.mit.theta.frontend.benchmark\build\libs\theta-sts.jar" "theta-sts.jar" /Y
copy "..\..\lib\*.dll" "*.dll"