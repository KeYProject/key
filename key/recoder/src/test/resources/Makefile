SOURCE_BASEDIR=src
DOC_BASEDIR=doc
DOC_SRCDIR=doc/examples/src/

DOC_PACKAGES=recoder.testsuite 
COMPILE_PACKAGES=$(DOC_PACKAGES) recoder.testsuite recoder.testsuite.basic recoder.testsuite.basic.analysis recoder.testsuite.basic.syntax testdata samples 
JAR_FILE=tests.jar
LIBS=../3rdpartylibs/junit.jar:../3rdpartylibs/bsh-1.2b2.jar:../doc/examples/examples.jar
LIBS_NODD=3rdpartylibs/junit.jar:3rdpartylibs/bsh-1.2b2.jar:doc/examples/examples.jar

SOURCE_DIRS=$(foreach dir, $(subst .,/,$(COMPILE_PACKAGES)), $(SOURCE_BASEDIR)/$(dir))
SOURCE_FILES=$(foreach dir, $(SOURCE_DIRS), $(wildcard $(dir)/*.java))
TARGETS=$(addsuffix .class, $(basename $(SOURCE_FILES)))
CLASSES=$(foreach dir, $(SOURCE_DIRS), $(subst $$,\$$,$(wildcard $(dir)/*.class)))

#JAVAC=jikes -O +P -classpath $(CLASSPATH):$(SOURCE_BASEDIR):../$(SOURCE_BASEDIR)
JAVAC=javac -sourcepath $(SOURCE_BASEDIR):$(DOC_SRCDIR) -classpath $(CLASSPATH):$(SOURCE_BASEDIR):../$(SOURCE_BASEDIR):$(LIBS)

all:	clean build jar doc

build: $(TARGETS)

clean:
	@rm -f $(CLASSES) $(JAR_FILE) $(DOC_BASEDIR)/*.html $(DOC_BASEDIR)/package-list
	@rm -fr $(DOC_BASEDIR)/testing

doc: ZERO
	@(javadoc -sourcepath src -classpath $(LIBS) -d ../$(DOC_BASEDIR) $(DOC_PACKAGES))

jar: $(JAR_FILE)

$(JAR_FILE):
	@(cd $(SOURCE_BASEDIR); jar cf $(JAR_FILE) `find . -name "*.class"` `find . -name "*.gif"`)
	@mv $(SOURCE_BASEDIR)/$(JAR_FILE) .
	@jar tf $(JAR_FILE)

%.class: %.java
	@$(JAVAC) $<
	@echo -n .
	@rm -f $(JAR_FILE)

tests:	build jar
	@(cd ..; java -classpath recoder.jar:test/tests.jar:$(LIBS_NODD):test/ recoder.testsuite.CompleteTestSuite; cd ..)

ZERO:
# special target, leave empty


