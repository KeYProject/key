# PROJECT 53  = key-public/key
DEPLOYURL=https://git.key-project.org/api/v4/projects/35/packages/maven

MVNDEPLOY="mvn -s settings.xml deploy:deploy-file -DrepositoryId=gpr -Durl=$DEPLOYURL"


# recoderkey
$MVNDEPLOY -DpomFile=recoderKey.pom.xml -Dfile=../../key.core/lib/recoderkey.jar

# docking-frames-core
#$MVNDEPLOY -DpomFile=docking-frames-core.pom.xml -Dfile=../../key.ui/lib/docking-frames-core.jar

# docking-frames-common
#$MVNDEPLOY -DpomFile=docking-frames-common.pom.xml -Dfile=../../key.ui/lib/docking-frames-common.jar
