BASENAME=examples
RECODER=../..
PACKAGES=$(shell cd $(SRC_DIR); find -type d -not -name CVS -not -name resources | sed "s/\//\./g")
SRC_DIR=src
SOURCE_DIRS=$(foreach dir, $(subst .,/,$(PACKAGES)), $(SRC_DIR)/$(dir)) .

SOURCES=$(foreach dir, $(SOURCE_DIRS), $(wildcard $(dir)/*.java))
TARGETS=$(addsuffix .class, $(basename $(SOURCES)))
CLASSES=$(foreach dir, $(SOURCE_DIRS), $(subst $$,\$$,$(wildcard $(dir)/*.class)))
TEMPORARY_DIR=output
JAR_FILE=$(BASENAME).jar
LIBS=../../3rdpartylibs/bsh-1.2b2.jar

#JAVAC=jikes
JAVAC=javac

%.class: %.java
	@$(JAVAC) -classpath .:$(RECODER)/src:$(SRC_DIR):$(CLASSPATH):$(LIBS) $<
	@echo -n .

all: build cleansrc cleantmp

jar: $(TARGETS)
	@(cd $(SRC_DIR); jar cf $(JAR_FILE) `find -name "*.class" -o -name "*.gif" -o -name "*.jpg" -o -name "*.bsh" -o -name "*.html"`; mv $(JAR_FILE) ..)
	@echo

build:	cleanjar jar
	@echo

clean: cleanjar cleansrc cleantmp

cleanjar: ZERO
	@rm -f $(JAR_FILE)

cleansrc: ZERO
	@rm -f $(CLASSES)

cleantmp: ZERO
	@rm -fr $(TEMPORARY_DIR)/*

run: build
	java -cp .:$(JAR_FILE):$(RECODER)/src:$$CLASSPATH sourcerer.Main converter.prj


ZERO:
