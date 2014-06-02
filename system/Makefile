# This file is part of KeY - Integrated Deductive Software Design 
#
# Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
#                         Universitaet Koblenz-Landau, Germany
#                         Chalmers University of Technology, Sweden
# Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
#                         Technical University Darmstadt, Germany
#                         Chalmers University of Technology, Sweden
#
# The KeY system is protected by the GNU General 
# Public License. See LICENSE.TXT for details.

SHELL=/bin/sh
# comon prefix
PFX=de/uka/ilkd/key/
# source directory
SRC=src/
# test directory
TEST=test/

#
#the path where to put the binaries.  This should be different from
#the source path (.), otherwise `make clean' will delete the 
#source tree.
BINARYPATH=binary/

# generated source path
export GENERATED_SRC_PATH=genSrc/

#the path where the resources are put (images etc.)
RESOURCEPATH=./resources/

#include configuration information
sinclude ./Makefile.mk

ifeq "$(JAVA)" ""
JAVA=$(shell which java)
endif

# enables optimization and removes debug info (such as line tables)
#COMMON_OPTIONS=-O -g:none -d $(BINARYPATH)

COMMON_OPTIONS=-g -d $(BINARYPATH)
OPTIONS=$(COMMON_OPTIONS)



GIT_AVAILABLE=$(shell which git)

ifneq ($(strip $(wordlist 1,1,$(GIT_AVAILABLE))),no) 
GIT=$(shell which git)
endif

GIT_REPOS_AVAILABLE=$(wildcard ../.git/objects)

ifeq "$(GIT_REPOS_AVAILABLE)" ""
  GIT=
endif

SHA1=ownVersion

ifeq "$(KEY_VERSION_SHORT)" "" 
  KEY_VERSION_SHORT=0.0.0
endif

ifneq "$(GIT)" "" 
   SHA1:=$(shell $(GIT) show | grep commit)
   SHA1:=$(wordlist 2,2,$(SHA1))
   ifeq "$(KEY_VERSION_SHORT)" "0.0.0" 
     KEY_VERSION_SHORT:=$(shell $(GIT) log --pretty=one | wc -l)
     KEY_VERSION_SHORT:=$(wordlist 1,1,$(KEY_VERSION_SHORT))
     KEY_VERSION_SHORT:=2.3.$(KEY_VERSION_SHORT)
   endif
endif

ifeq "$(KEY_VERSION_LONG)" ""
KEY_VERSION_LONG=$(KEY_VERSION_SHORT)_$(SHA1)
endif

export KEY_VERSION_LONG
export KEY_VERSION_SHORT

ifeq "$(JAVAC)" ""
JAVAC=javac
else 
ifeq ($(JAVAC),jikes) 
JAVAC:=javac
endif
endif

ifeq "$(ANTLR)" ""
ANTLR=$(JAVA) -cp $(GENERATED_SRC_PATH):$(CLASSPATH) antlr.Tool
endif

ifeq "$(ANTLR3)" ""
ANTLR3=$(JAVA) -cp $(GENERATED_SRC_PATH):$(CLASSPATH) org.antlr.Tool
endif

ifeq ($(JAVAC),ajc)
  OPTIONS=$(COMMON_OPTIONS) -nowarn -classpath $(ASPECTJRTPATH):$(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
else
  OPTIONS=$(COMMON_OPTIONS) -J-Xmx512m -nowarn -classpath $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
endif

JAVACC_MAIN=javacc

## nice source links
JAVADOC=javadoc
JAVADOC_OPTIONS=-use -quiet -breakiterator -linksource -J-Xmx1024m


ANTLR_PARSER= \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLParser.java

ANTLR3_PARSER= \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYParser.java \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreParser.java


JAVACC_PARSER= \
	$(GENERATED_SRC_PATH)$(PFX)parser/schemajava/SchemaJavaParserConstants.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/schemajava/ParseException.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/schemajava/TokenMgrError.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/schemajava/SchemaJavaParserTokenManager.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/schemajava/SchemaJavaParser.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/schemajava/Token.java 

PROOFJAVA_PARSER= \
	$(GENERATED_SRC_PATH)$(PFX)parser/proofjava/ProofJavaParserConstants.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/proofjava/ParseException.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/proofjava/TokenMgrError.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/proofjava/ProofJavaParserTokenManager.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/proofjava/ProofJavaParser.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/proofjava/Token.java \




.PHONY: all
all:	javahomeset branding
	@$(MAKE) -s all_gen


## create javadoc
.PHONY: doc
doc: argfile 
	@mkdir -p doc
## old doc generation	
#	@find de/ | grep "\.java" | grep -v "\~" | xargs javadoc -use -classpath $(CLASSPATH):$(BINARYPATH) -d doc 

## new one produces better output (package index) but is more fragile.
## didn't want to use perl ;)
	@find $(SRC) -name '*.java' | xargs grep -h "^package\|^overview" |\
	cut -d" " -f2 | cut -d";" -f1 | sort | uniq | grep "^de.uka" | \
	xargs $(JAVADOC) $(JAVADOC_OPTIONS) -classpath $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH) \
	-sourcepath $(GENERATED_SRC_PATH):$(SRC):$(TEST) -d doc \
	-link http://recoder.sourceforge.net/doc/api \
	-link http://docs.oracle.com/javase/7/docs/api/ \
	-link http://www.antlr2.org/javadoc/ \
	-link http://www.antlr3.org/api/Java/ \
	-windowtitle "KeY API Documentation" \
	-doctitle "KeY API Documentation ($(KEY_VERSION_LONG))" \
	-header "KeY $(KEY_VERSION_LONG)" \
	-private -author -version -J-Xmx512m



## create distribution package
.PHONY: dist
dist:	branding all
	@echo "[creating distribution directory structure]"
	@mkdir -p ../dist
	@mkdir -p dist/key/
	@cp -r $(BINARYPATH)/* dist/key/
	@cp -r $(RESOURCEPATH)/* dist/key/
	@jar cMf dist/key/examples.jar -C ../examples/firstTouch .
# for setup.jar
	@mkdir -p dist/setup/de/uka/ilkd/key/util/
	@cp -r $(BINARYPATH)/de/uka/ilkd/key/util/* dist/setup/de/uka/ilkd/key/util/
	@cp -r $(RESOURCEPATH)/de/uka/ilkd/key/util/install/* dist/setup/de/uka/ilkd/key/util/install/
	@mkdir -p dist/setup/de/uka/ilkd/key/gui/
	@cp -r $(BINARYPATH)/de/uka/ilkd/key/gui/IconFactory* dist/setup/de/uka/ilkd/key/gui/
	@cp -r $(RESOURCEPATH)/de/uka/ilkd/key/gui/* dist/setup/de/uka/ilkd/key/gui/
	@find dist -name '*~' -exec rm \{\} \; 
	@echo "[creating jar-file]"
	@jar cfm key.jar resources/MANIFEST.MF -C dist/key/ .
	@jar cfm setup.jar resources/de/uka/ilkd/key/util/install/MANIFEST.MF -C dist/setup/ .
	@tar -czvf ../dist/KeY-$(KEY_VERSION_LONG).tgz key.jar setup.jar \
			-C ../ LICENSE.TXT -C system/dist/key examples.jar 
	@zip -j ../dist/KeY-${KEY_VERSION_LONG}.zip key.jar setup.jar dist/key/examples.jar ../LICENSE.TXT 
	@cp ../README.install.bytecode ../dist/README-$(KEY_VERSION_LONG).txt
	@echo "[deleting distribution directory structure]"
	@rm -rf dist

.PHONY: jar
jar:	all
	@echo "[creating jar-file]"
	@jar cfm key.jar resources/MANIFEST.MF -C binary/ .

.PHONY: dist_src
dist_src: distclean branding javaFiles
	@mkdir -p ../dist
	@rm -rf /tmp/keydist-$(USER)
	@echo "[creating source archive]"
	@mkdir -p /tmp/keydist-$(USER)
	@ln -s "$(shell cd ..;pwd)" /tmp/keydist-$(USER)/key-$(KEY_VERSION_LONG)
	@tar -C/tmp/keydist-$(USER) --dereference  \
        -cf /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar --exclude=key-$(KEY_VERSION_LONG)/.git/'*' \
	--exclude=key-$(KEY_VERSION_LONG)/key-ext-jars/'*' --exclude=key-$(KEY_VERSION_LONG)/eclipse key-$(KEY_VERSION_LONG)
	@tar -rf /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar -C /tmp/keydist-$(USER) key-$(KEY_VERSION_LONG)/eclipse/
	@gzip /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar
	@mv /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar.gz ../dist/KeY-$(KEY_VERSION_LONG)-src.tgz
	@cp /tmp/keydist-$(USER)/key-$(KEY_VERSION_LONG)/README.install.source ../dist/README-$(KEY_VERSION_LONG)-src.txt
	@echo "[done]"


.PHONY: clean
## clean
clean:
	@echo [deleting generated .java-files]
	@/bin/rm -rf $(GENERATED_SRC_PATH)
	@echo [deleting binaries]
	@/bin/rm -rf $(BINARYPATH)
	@echo [deleting distribution]
	@/bin/rm -rf ../dist
	@/bin/rm -rf proofExamples/statistics.csv

#help files of the makefile (without the GenMakefile)

	@rm -f javaFiles
	@rm -f unit_manager.log 
	@rm -f msg.txt
	@rm -f argfile.aspects
	@rm -f argfile.normal 
	@rm -f argfile.other
	@rm -f argfile
	@rm -f error.msg
	@rm -f critical.msg
	@rm -f warning.msg
	@rm -f -r ./qwe

.PHONY: realclean
realclean: clean

#help files of the makefile
	@rm -f Makefile.mk

.PHONY: distclean
distclean: realclean
	@rm -f setup.jar
	@rm -f key.jar
	@rm -f KeY.tgz
	@rm -f keySource.tgz

.PHONY: all_gen
all_gen: 
	@$(MAKE) -s all_hlp   	

.PHONY: all_hlp
all_hlp: argfile.normal $(ANTLR_PARSER) $(ANTLR3_PARSER) $(JAVACC_PARSER) $(PROOFJAVA_PARSER) $(DIFF_PARSER) copy
ifeq "$(BRANDING)" ""
# always update SHA1 hash in order to get useful bug reports		
	@echo $(SHA1) > ${BINARYPATH}/de/uka/ilkd/key/util/sha1
	@echo $(KEY_VERSION_SHORT) > ${BINARYPATH}/de/uka/ilkd/key/util/version
else
endif
	@rm -f error.msg
	@rm -f critical.msg
	@rm -f warning.msg
	@echo [KeY is being compiled]
	@echo $(ANTLR_PARSER) $(ANTLR3_PARSER) $(JAVACC_PARSER) \
	      $(PROOFJAVA_PARSER) $(DIFF_PARSER) \
              | xargs -n1 echo > argfile.other 
ifeq ($(JAVAC),ajc)
	@grep -v "^#" aspects/aspects.config > argfile.aspects
else
	@rm -f argfile.aspects
	@touch argfile.aspects
endif	
	@cat argfile.normal argfile.other argfile.aspects | sort -u > argfile
	@$(JAVAC) $(OPTIONS) @argfile 2>>error.msg || true
	@./success

.PHONY: copy
copy: javahomeset
	@echo "[copying resources]"
	@cp -r $(RESOURCEPATH)/* $(BINARYPATH)


branding:
ifeq "$(BRANDING)" ""
	@echo "[No Branding. Set environment variable BRANDING to activate branding.]"
else
	@echo "[Branding]"
	@echo $(SHA1) > resources/de/uka/ilkd/key/util/sha1
	@echo $(KEY_VERSION_SHORT) > resources/de/uka/ilkd/key/util/version
#	@./brandManifest.sh ../eclipse/KeYExternalLibraries/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
#	@./brandManifest.sh ../eclipse/org.key-project.core/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
#	@./brandManifest.sh ../eclipse/KeYPlugin/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
#	@./brandManifest.sh ../eclipse/VisualDebugger/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
#	@./brandPlugin.sh ../eclipse/ProofVisualization/plugin.xml $(KEY_VERSION_SHORT)
# we must replace the feature url and version tag in site.xml 
#	@./brandPlugin.sh ../eclipse/KeYFeature/site.xml $(KEY_VERSION_SHORT)
#	@./brandPlugin.sh ../eclipse/KeYFeature/feature.xml $(KEY_VERSION_SHORT)
#	@./brandFeatureSite.sh ../eclipse/KeYFeature/site.xml $(KEY_VERSION_SHORT)
endif

javaFiles: 
ifneq ("$(GIT)","")
	@$(GIT) ls-files | grep "\.java" | grep -v "aspects" | grep -v "gjava" | grep -v "\.java\." | grep -v "resources/" | sort > javaFiles
else
	@find $(SRC)/de/ -name \*\.java  | grep -v "aspects" | grep -v "gjava" | grep -v "\.java\." | grep -v "resources/" | sort > javaFiles
endif

argfile.normal: javaFiles
	@echo [Collecting Java files to compile]
	@cat javaFiles > argfile.normal
	@echo "test/TestKey.java" >> argfile.normal 
## make gjava -> java


$(JAVACC_PARSER) \
	: $(SRC)$(PFX)parser/schemajava/SchemaJavaParser.jj
	@echo [creating parser for schematic java in taclets]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/schemajava
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/schemajava/*.java $@
	@cp $(SRC)$(PFX)parser/schemajava/Token.java.source $(GENERATED_SRC_PATH)$(PFX)parser/schemajava/Token.java	
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/schemajava $< 

$(PROOFJAVA_PARSER) \
	: $(SRC)$(PFX)parser/proofjava/ProofJavaParser.jj
	@echo [create parser for extended java in proofs]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/proofjava
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/proofjava/*.java $@
	@cp $(SRC)$(PFX)parser/proofjava/Token.java.source $(GENERATED_SRC_PATH)$(PFX)parser/proofjava/Token.java
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/proofjava $< 

$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexer.java \
	: $(SRC)$(PFX)parser/KeYLexer.g
	@echo [creating KeYLexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser
	@$(ANTLR3) -fo $(GENERATED_SRC_PATH)$(PFX)parser $<

$(GENERATED_SRC_PATH)$(PFX)parser/KeYParser.java \
	: $(SRC)$(PFX)parser/KeYParser.g \
	  $(SRC)$(PFX)parser/KeYLexer.g
	@echo [creating global KeY parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser
	@$(ANTLR3) -glib $(SRC)$(PFX)parser/KeYLexer.g \
			-fo $(GENERATED_SRC_PATH)$(PFX)parser $<

$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexer.java \
$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexerTokenTypes.java \
	: $(SRC)$(PFX)parser/simplify/lexer.g
	@echo [creating SimplifyLexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/simplify
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -o $(GENERATED_SRC_PATH)$(PFX)parser/simplify $<

$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyParser.java \
	: $(SRC)$(PFX)parser/simplify/simplify.g \
	  $(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexerTokenTypes.txt
	@echo [creating Simplify parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/simplify
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -glib $(SRC)$(PFX)parser/simplify/lexer.g \
			 -o $(GENERATED_SRC_PATH)$(PFX)parser/simplify $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexer.java \
	: $(SRC)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexer.g
	@echo [creating JML pre lexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation
	@$(ANTLR3) -fo $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreParser.java \
	: $(SRC)$(PFX)speclang/jml/pretranslation/KeYJMLPreParser.g \
	  $(SRC)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexer.g
	@echo [creating JML pre parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation
	@$(ANTLR3) -glib $(SRC)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexer.g \
			-fo $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexer.java \
$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexerTokenTypes.java \
	: $(SRC)$(PFX)speclang/jml/translation/jmllexer.g
	@echo [creating JML lexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -o $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLParser.java \
	: $(SRC)$(PFX)speclang/jml/translation/jmlparser.g \
	  $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexerTokenTypes.txt
	@echo [creating JML parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -glib $(SRC)$(PFX)speclang/jml/translation/jmllexer.g \
	                 -o $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation $<

.PHONY: help
help:
	@echo
	@echo " (g)make"
	@echo "    help:      prints this message"
	@echo
	@echo "    all:       compiles the KeY-system"
	@echo
	@echo "    dist:      'all' + creates a binary distribution "
	@echo "               (../KeY.tgz containing an installation script, "
	@echo "               the compiled KeY-system without sources, "
	@echo "               without external libraries)"
	@echo
	@echo "    dist_src:  'realclean' + creates a sourcecode distribution"
	@echo "               (../KeY.src.tgz containing all source files but "
	@echo "               without the external libraries)" 
	@echo
	@echo "    clean:     deletes all generated .java and .class files"
	@echo "               but not the configuration of ext. libraries"
	@echo
	@echo "    realclean: 'clean' + deletes libraries configuration"
	@echo
	@echo "    doc:       creates the documentation of the KeY-system"
	@echo
	@echo "    eclipse-plug-in: 'dist' + builds the eclipse plug-in"
	@echo "                     needs ECLIPSE_HOME to be pointing to your"
	@echo "                     eclipse application"

.PHONY: javahomeset
javahomeset:
	@./checkEnvironment
	@mkdir -p $(BINARYPATH)

# eclipse plug-in:
eclipse-plug-in: dist
	@cd ../eclipse/KeYFeature && $(MAKE)
	@rm -fr $(BINARYPATH)$(PFX)casetool/eclipse
	@mkdir -p $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/features
	@mkdir -p $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins
	@cp  ../eclipse/KeYFeature/site.xml $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/ 
	@cp  ../eclipse/KeYFeature/KeY_Feature_*.jar $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/features/
	@cp  ../eclipse/KeYPlugin/KeYPlugin_*.jar $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins/
	@cp  ../eclipse/ProofVisualization/ProofVisualization_*.jar $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins
	@cp  ../eclipse/org.key-project.core/org.key_project.core_* $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins
	@cp  ../eclipse/KeYExternalLibraries/KeYExternalLibraries_1* $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins

#mostly useful for creating the COST tool distribution
localinst:
	@echo "Do not forget to make jar first"
	@mkdir -p /usr/lib/key
	@cp -r ../bin /usr/lib/key
	@mkdir -p /usr/lib/key/key-ext-jars
	@cp $(KEY_LIB)/recoderKey.jar /usr/lib/key/key-ext-jars
	@cp $(KEY_LIB)/antlr.jar /usr/lib/key/key-ext-jars
	@cp key.jar /usr/lib/key
	@sed -i 's/system\/binary\//key.jar/g' /usr/lib/key/bin/*
	@ln -sf /usr/lib/key/bin/runProver /usr/bin/
