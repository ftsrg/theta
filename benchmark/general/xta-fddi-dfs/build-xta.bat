pushd "../../../"
call gradlew.bat xtaMain
popd
copy "..\..\..\hu.bme.mit.theta.frontend.benchmark\build\libs\theta-xta.jar" "theta-xta.jar" /Y
copy "..\..\..\lib\*.dll" "*.dll"