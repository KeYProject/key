DEPLOYURL=https://maven.pkg.github.com/KeYProject/key

MVNDEPLOY="mvn -s settings.xml deploy:deploy-file -DrepositoryId=gpr -Durl=$DEPLOYURL"


# recoderkey
# $MVNDEPLOY -DpomFile=recoderKey.pom.xml -Dfile=../../key.core/lib/recoderkey.jar

# docking-frames-core
#$MVNDEPLOY -DpomFile=docking-frames-core.pom.xml -Dfile=../../key.ui/lib/docking-frames-core.jar

$MVNDEPLOY -DpomFile=docking-frames-common.pom.xml -Dfile=../../key.ui/lib/docking-frames-common.jar
