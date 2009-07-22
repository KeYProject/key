# This file is part of KeY - Integrated Deductive Software Design 
# Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
#                         Universitaet Koblenz-Landau, Germany
#                         Chalmers University of Technology, Sweden 
#
# The KeY system is protected by the GNU General Public License. 
# See LICENSE.TXT for details.

SHELL=/bin/sh
#comon prefix
PFX=de/uka/ilkd/key/

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

SHA1=ownVersion

ifeq "$(KEY_VERSION_SHORT)" "" 
  KEY_VERSION_SHORT=0.0.0
endif

ifneq "$(GIT)" "" 
 ifneq "$(GIT_REPOS_AVAILABLE)" ""
   SHA1:=$(shell $(GIT) show | grep commit)
   SHA1:=$(wordlist 2,2,$(SHA1))
   ifeq "$(KEY_VERSION_SHORT)" "0.0.0" 
     KEY_VERSION_SHORT:=$(shell $(GIT) log --pretty=one | wc -l)
     KEY_VERSION_SHORT:=$(wordlist 1,1,$(KEY_VERSION_SHORT))
     KEY_VERSION_SHORT:=1.5.$(KEY_VERSION_SHORT)
   endif
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

ifeq ($(JAVAC),ajc)
  OPTIONS=$(COMMON_OPTIONS) -nowarn -classpath $(ASPECTJRTPATH):$(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
else
  ifeq ($(JAVAC),ejc)      
    OPTIONS=$(COMMON_OPTIONS) -warn:uselessTypeCheck,localHiding,fieldHiding,tasks\(TODO\|HACK\|%%%\)  -source 1.5 -target 1.5 -classpath $(JAVA_HOME)/jre/lib/rt.jar:$(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
  else 
    OPTIONS=$(COMMON_OPTIONS) -J-Xmx512m -nowarn -source 1.5 -target 1.5 -classpath $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
  endif
endif


#for JavaCC 3.0:
JAVACC_MAIN=javacc
#for JavaCC 2.0:
#JAVACC_MAIN=COM.sun.labs.javacc.Main


## nice source links
JAVADOC=javadoc
JAVADOC_OPTIONS=-use -quiet -breakiterator -linksource -J-Xmx512m

## KeY config
PLUG_IN_FILTER?="(none)"
export PLUG_IN_FILTER
COMPILE_GF?=--with-gf
export COMPILE_GF

# this part creates .java-files from .gjava files
#	rule/SLListOfRule rule/SLListOfRuleApp \

GENERATED_ITERATORS=proof/IteratorOfNode \
	logic/op/IteratorOfBoolean \
	rule/IteratorOfListOfNoPosTacletApp \
	ldt/IteratorOfLDT \
	java/abstraction/IteratorOfListOfType \
	rule/IteratorOfVariableCondition \
	logic/op/IteratorOfOperator

GENERATED_LISTS=logic/SLListOfTerm \
	logic/op/SLListOfQuantifiableVariable \
	logic/SLListOfNamed \
	logic/op/SLListOfSchemaVariable \
	rule/SLListOfNewVarcond \
	rule/SLListOfVariableCondition \
	logic/op/SLListOfLogicVariable \
	logic/op/SLListOfParsableVariable \
	logic/op/SLListOfOperator \
	logic/op/SLListOfUpdateableOperator \
	collection/SLListOfString \
	logic/op/SLListOfMetavariable \
	logic/SLListOfRenamingTable \
	collection/SLListOfDouble \
	logic/SLListOfConstrainedFormula \
	rule/SLListOfBuiltInRule \
	rule/SLListOfTaclet rule/SLListOfFindTaclet \
	rule/SLListOfNoFindTaclet \
	rule/SLListOfRuleSet rule/SLListOfTacletGoalTemplate \
	rule/SLListOfNotFreeIn  \
	rule/SLListOfNewDependingOn  \
	rule/SLListOfVariableCondition  \
	rule/SLListOfTacletPrefix  \
	rule/SLListOfObject \
	logic/SLListOfInteger proof/SLListOfGoal \
	proof/SLListOfNode \
	rule/inst/SLListOfTacletInstantiations \
	rule/inst/SLListOfSVInstantiations \
	rule/SLListOfTacletApp \
	rule/SLListOfNoPosTacletApp \
	rule/inst/SLListOfProgramSVEntry \
	rule/inst/SLListOfInstantiationEntry \
	java/SLListOfStatement \
	java/SLListOfProgramElement \
	rule/SLListOfPosTacletApp \
	logic/op/SLListOfProgramVariable \
	logic/op/SLListOfProgramMethod \
	java/declaration/SLListOfVariableSpecification \
	java/abstraction/SLListOfMethod \
	logic/op/SLListOfProgramMethod \
	java/abstraction/SLListOfClassType \
	java/abstraction/SLListOfType \
	java/abstraction/SLListOfKeYJavaType \
	java/abstraction/SLListOfField \
	rule/SLListOfMatchConditions \
	rule/SLListOfIfFormulaInstantiation \
	java/abstraction/SLListOfConstructor \
	logic/SLListOfConstraint \
	pp/SLListOfSequentPrintFilterEntry \
	proof/proofevent/SLListOfNodeReplacement \
	proof/proofevent/SLListOfNodeChange \
	proof/proofevent/SLListOfNodeChangesHolder \
	proof/incclosure/SLListOfSink \
	proof/SLListOfProof \
	logic/sort/SLListOfGenericSort \
	rule/inst/SLListOfGenericSortCondition \
	logic/op/SLListOfSortDependingSymbol \
	logic/SLListOfName \
	logic/op/SLListOfIProgramVariable \
	logic/SLListOfSequentChangeInfo \
	logic/SLListOfFormulaChangeInfo \
	proof/SLListOfTermTacletAppIndex \
	strategy/SLListOfRuleAppContainer \
	logic/SLListOfProgramElementName \
	proof/mgt/SLListOfQuantifierPrefixEntry \
	proof/SLListOfInstantiationProposer \
        speclang/SLListOfOperationContract \
	speclang/SLListOfClassInvariant \
	proof/init/SLListOfProofOblInput \
	rule/export/SLListOfTacletModelInfo \
	rule/export/SLListOfOptionModelInfo \
	rule/export/SLListOfRuleSetModelInfo \
	rule/export/SLListOfDisplayNameModelInfo \
	rule/export/SLListOfCategoryModelInfo \
	logic/SLListOfNamespace \
	speclang/translation/SLListOfSLExpression \
	speclang/translation/SLListOfSLExpressionResolver \
	speclang/SLListOfPositionedString \
        speclang/jml/pretranslation/SLListOfTextualJMLConstruct \
	ldt/SLListOfLDT \
        rule/metaconstruct/arith/SLListOfMonomial \
	strategy/feature/instantiator/SLListOfCPBranch \
	java/SLListOfComment \
	strategy/SetAsListOfStrategyFactory \
	pp/SLListOfRange

GENERATED_SETS=logic/SetAsListOfTerm collection/SetAsListOfString \
	rule/SetAsListOfTaclet rule/SetAsListOfRuleApp \
	rule/SetAsListOfNoPosTacletApp \
	logic/op/SetAsListOfQuantifiableVariable \
	logic/op/SetAsListOfSchemaVariable \
	rule/SetAsListOfTacletApp \
	proof/SetAsListOfProof \
	java/SetAsListOfExpression \
	logic/op/SetAsListOfProgramVariable \
	logic/op/SetAsListOfProgramMethod \
	logic/sort/SetAsListOfSort \
	logic/sort/SetAsListOfGenericSort \
	logic/op/SetAsListOfIProgramVariable \
	logic/op/SetAsListOfMetavariable \
	logic/SetAsListOfChoice \
	logic/SetAsListOfNamed \
	logic/SetAsListOfLocationDescriptor \
        logic/op/SetAsListOfLogicVariable \
        proof/SetAsListOfGoalChooserBuilder \
	speclang/SetAsListOfClassInvariant \
        speclang/SetAsListOfOperationContract \
        speclang/SetAsListOfLoopInvariant \
	strategy/SetAsListOfStrategyFactory \
	java/abstraction/SetAsListOfKeYJavaType \
	proof/mgt/SetAsListOfContractWithInvs \
	strategy/quantifierHeuristics/SetAsListOfTrigger\
	strategy/quantifierHeuristics/SetAsListOfSubstitution \
	java/statement/SetAsListOfLoopStatement \
        proof/SetAsListOfGoalChooserBuilder \
	strategy/SetAsListOfStrategyFactory \
	logic/op/SetAsListOfUpdateableOperator \
	speclang/SetAsListOfPositionedString \
        logic/op/SetAsListOfModality

GENERATED_MAPS=	collection/MapAsListFromIntegerToString \
	logic/op/MapAsListFromQuantifiableVariableToInteger \
	logic/op/MapAsListFromSchemaVariableToTerm \
	logic/op/MapAsListFromSchemaVariableToInstantiationEntry \
	logic/op/MapAsListFromLogicVariableToTerm \
	logic/op/MapAsListFromSchemaVariableToTacletPrefix \
	logic/sort/MapAsListFromGenericSortToSort \
	logic/op/MapAsListFromNameToSortDependingSymbol \
	logic/op/MapAsListFromSchemaVariableToSchemaVariable \
	proof/MapAsListFromConstrainedFormulaToTermTacletAppIndex \
	proof/proofevent/MapAsListFromNodeToNodeChangesHolder \
	logic/op/MapAsListFromQuantifiableVariableToTerm \
	logic/op/MapAsListFromQuantifiableVariableToMetavariable 

GENERATED_ARRAYS=java/ArrayOfProgramElementExtnullInnull \
	java/ArrayOfStatementExtProgramElementInnull \
	java/ArrayOfExpressionExtProgramElementInnull \
	java/ArrayOfLoopInitializerExtProgramElementInnull \
	java/ArrayOfImportExtProgramElementInnull \
	java/declaration/ArrayOfMemberDeclarationExtProgramElementInde.uka.ilkd.key.java \
	java/declaration/ArrayOfVariableSpecificationExtProgramElementInde.uka.ilkd.key.java \
	java/declaration/ArrayOfFieldSpecificationExtVariableSpecificationInnull \
	java/declaration/ArrayOfImplicitFieldSpecificationExtFieldSpecificationInnull \
	java/declaration/ArrayOfModifierExtProgramElementInde.uka.ilkd.key.java \
	java/declaration/ArrayOfParameterDeclarationExtProgramElementInde.uka.ilkd.key.java \
	java/declaration/ArrayOfTypeDeclarationExtProgramElementInde.uka.ilkd.key.java \
	java/statement/ArrayOfBranchExtProgramElementInde.uka.ilkd.key.java \
	java/reference/ArrayOfTypeReferenceExtProgramElementInde.uka.ilkd.key.java \
	logic/ArrayOfProgramPrefixExtnullInnull \
	logic/op/ArrayOfUpdateableOperatorExtnullInnull \
	logic/op/ArrayOfQuantifiableVariableExtnullInnull \
	logic/op/ArrayOfIProgramVariableExtProgramElementInde.uka.ilkd.key.java \
	logic/ArrayOfTermExtnullInnull \
	logic/sort/ArrayOfSortExtnullInnull \
	java/abstraction/ArrayOfKeYJavaTypeExtnullInde.uka.ilkd.key.java.abstraction \
	strategy/feature/ArrayOfFeatureExtnullInnull

GENERATED_HEAPS= logic/LeftistHeapOfInteger \
	strategy/LeftistHeapOfRuleAppContainer

GENERATED_VECTORS_STACKS = util/SimpleStackOfExtList 

GEN_FILES=$(GENERATED_MAPS) $(GENERATED_VECTORS_STACKS) $(GENERATED_ARRAYS) $(GENERATED_LISTS) $(GENERATED_SETS) \
	$(GENERATED_ITERATORS) $(GENERATED_HEAPS)

ANTLR_PARSER= \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexerTokenTypes.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYParser.java \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreParser.java \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLParser.java \
	$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocParser.java \
	$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocTreeWalker.java 


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

DIFF_PARSER= \
	$(GENERATED_SRC_PATH)$(PFX)parser/diffparser/DiffParserConstants.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/diffparser/ParseException.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/diffparser/TokenMgrError.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/diffparser/DiffParserTokenManager.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/diffparser/DiffParser.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/diffparser/Token.java


## generic java support
JAVAFILES=$(GEN_FILES:%=$(PFX)%.java) 

.PHONY: all
all:	javahomeset branding
	@$(MAKE) -s all_gen


## create javadoc
.PHONY: doc
doc: argfile $(JAVAFILES)
	@mkdir -p doc
## old doc generation	
#	@find de/ | grep "\.java" | grep -v "\~" | xargs javadoc -use -classpath $(CLASSPATH):$(BINARYPATH) -d doc 

## new one produces better output (package index) but is more fragile.
## didn't want to use perl ;)
	@find de/ -name '*.java' | xargs grep -h "^package\|^overview" |\
	cut -d" " -f2 | cut -d";" -f1 | sort | uniq | grep "^de.uka" | \
	xargs $(JAVADOC) $(JAVADOC_OPTIONS) -source 1.5 -classpath $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH) \
	-sourcepath $(GENERATED_SRC_PATH):. -d doc \
	-link http://recoder.sourceforge.net/doc/api \
	-link http://java.sun.com/j2se/1.5.0/docs/api/ \
	-link http://www.antlr.org \
	-windowtitle "KeY API Documentation" \
	-doctitle "KeY API Documentation ($(KEY_VERSION_LONG))" \
	-header "KeY $(KEY_VERSION_LONG)" \
	-private -author -version -J-Xmx256m



## create distribution package
.PHONY: dist
dist:	branding all
	@echo "[creating distribution directory structure]"
	@mkdir -p ../dist
	@mkdir -p dist/key/
	@cp -r $(BINARYPATH)/* dist/key/
	@cp -r $(RESOURCEPATH)/* dist/key/
	@cp -r ../examples dist/key/
# for setup.jar
	@mkdir -p dist/setup/de/uka/ilkd/key/util/
	@cp -r $(BINARYPATH)/de/uka/ilkd/key/util/* dist/setup/de/uka/ilkd/key/util/
	@cp -r $(RESOURCEPATH)/de/uka/ilkd/key/util/install/* dist/setup/de/uka/ilkd/key/util/install/
	@mkdir -p dist/setup/de/uka/ilkd/key/gui/
	@cp -r $(BINARYPATH)/de/uka/ilkd/key/gui/IconFactory* dist/setup/de/uka/ilkd/key/gui/
	@cp -r $(BINARYPATH)/de/uka/ilkd/key/gui/KeYFolderIcon* dist/setup/de/uka/ilkd/key/gui/
	@cp -r $(BINARYPATH)/de/uka/ilkd/key/gui/KeYControlIcon* dist/setup/de/uka/ilkd/key/gui/
	@cp -r $(RESOURCEPATH)/de/uka/ilkd/key/gui/* dist/setup/de/uka/ilkd/key/gui/
	@find dist -name '*~' -exec rm \{\} \; 
	@echo "[creating jar-file]"
	@jar cfm key.jar resources/MANIFEST.MF -C dist/key/ .
	@jar cfm setup.jar resources/de/uka/ilkd/key/util/install/MANIFEST.MF -C dist/setup/ .
	@tar -czvf ../dist/KeY-$(KEY_VERSION_LONG).tgz key.jar setup.jar -C ../ LICENSE.TXT
	@cp ../README.install.bytecode ../dist/README-$(KEY_VERSION_LONG).txt
	@echo "[deleting distribution directory structure]"
	@rm -rf dist

.PHONY: jar
jar:	all
	@echo "[creating jar-file]"
	@jar cfm key.jar resources/MANIFEST.MF -C binary/ .

.PHONY: dist_src
dist_src: distclean branding javaFiles
	@rm -rf /tmp/keydist-$(USER)
	@echo "[creating source archive]"
	@mkdir -p /tmp/keydist-$(USER)
	@ln -s $(shell cd ..;pwd) /tmp/keydist-$(USER)/key-$(KEY_VERSION_LONG)
	@tar -C/tmp/keydist-$(USER) --dereference  \
        -cvf /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar --exclude=key-$(KEY_VERSION_LONG)/.git/'*' \
	--exclude=key-$(KEY_VERSION_LONG)/key-ext-jars/'*' --exclude=key-$(KEY_VERSION_LONG)/eclipse key-$(KEY_VERSION_LONG)
	@tar -rf /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar -C /tmp/keydist-$(USER) key-$(KEY_VERSION_LONG)/eclipse/
	@gzip /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar
	@mv /tmp/keydist-$(USER)/KeY-$(KEY_VERSION_LONG)-src.tar.gz ../KeY-$(KEY_VERSION_LONG)-src.tgz
	@cp /tmp/keydist-$(USER)/key-$(KEY_VERSION_LONG)/README.install.source ../README-$(KEY_VERSION_LONG)-src.txt
	@echo "[done]"


.PHONY: clean
## clean
clean:
	@echo [deleting generated .java-files]
	@/bin/rm -rf $(GENERATED_SRC_PATH)
	@echo [deleting binaries]
	@/bin/rm -rf $(BINARYPATH)

#help files of the makefile (without the GenMakefile)

	@rm -f javaFiles
	@rm -f unit_manager.log 
	@rm -f msg.txt
	@rm -f argfile.aspects
	@rm -f argfile.generic
	@rm -f argfile.normal 
	@rm -f argfile.other
	@rm -f argfile
	@rm -f error.msg
	@rm -f critical.msg
	@rm -f warning.msg
	@rm -f gf.msg
	@rm -f -r ./qwe

.PHONY: realclean
realclean: clean

#help files of the makefile
	@rm -f GenMakefile
	@rm -f Makefile.mk

.PHONY: distclean
distclean: realclean
	@rm -f setup.jar
	@rm -f key.jar
	@rm -f KeY.tgz
	@rm -f keySource.tgz

.PHONY: all_gen
all_gen: genericMakefile
	@$(MAKE) -s all_hlp   	

.PHONY: all_hlp
all_hlp: argfile.normal $(JAVAFILES) $(ANTLR_PARSER) $(JAVACC_PARSER) $(PROOFJAVA_PARSER) $(KEYDOC_JAVAS) $(DIFF_PARSER) copyResources
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
	@echo $(ANTLR_PARSER) $(JAVACC_PARSER) \
	      $(PROOFJAVA_PARSER) $(DIFF_PARSER) \
              | xargs -n1 echo > argfile.other 
ifeq ($(JAVAC),ajc)
	@grep -v "^#" aspects/aspects.config > argfile.aspects
else
	@rm -f argfile.aspects
	@touch argfile.aspects
endif	
	@cat argfile.generic argfile.normal argfile.other argfile.aspects |\
              (grep -v $(PLUG_IN_FILTER) || true) | sort -u > argfile
	@$(JAVAC) $(OPTIONS) @argfile 2>>error.msg || true
	@./success

.PHONY: copyResources
copyResources: javahomeset
	@echo "[copying resources]"
	@cp -r $(RESOURCEPATH)/* $(BINARYPATH)


branding:
ifeq "$(BRANDING)" ""
	@echo "[No Branding. Set environment variable BRANDING to activate branding.]"
else
	@echo "[Branding]"
	@echo $(SHA1) > resources/de/uka/ilkd/key/util/sha1
	@echo $(KEY_VERSION_SHORT) > resources/de/uka/ilkd/key/util/version
	@./brandManifest.sh ../eclipse/KeYExternalLibraries/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
	@./brandManifest.sh ../eclipse/org.key-project.core/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
	@./brandManifest.sh ../eclipse/KeYPlugin/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
	@./brandManifest.sh ../eclipse/VisualDebugger/META-INF/MANIFEST.MF $(KEY_VERSION_SHORT)
	@./brandPlugin.sh ../eclipse/ProofVisualization/plugin.xml $(KEY_VERSION_SHORT)
# we must replace the feature url and version tag in site.xml 
	@./brandPlugin.sh ../eclipse/KeYFeature/site.xml $(KEY_VERSION_SHORT)
	@./brandPlugin.sh ../eclipse/KeYFeature/feature.xml $(KEY_VERSION_SHORT)
	@./brandFeatureSite.sh ../eclipse/KeYFeature/site.xml $(KEY_VERSION_SHORT)
endif

javaFiles: 
ifneq ("$(GIT)","")
	@$(GIT) ls-files | grep "\.java" | grep -v "aspects" | grep -v "gjava" | grep -v "\.java\." | grep -v "resources/" | sort > javaFiles
endif

argfile.normal: javaFiles
	@echo [Collecting Java files to compile]
	@cat javaFiles > argfile.normal
	@echo "TestKey.java" >> argfile.normal 
## make gjava -> java


$(JAVACC_PARSER) \
	: $(PFX)parser/schemajava/SchemaJavaParser.jj
	@echo [creating parser for schematic java in taclets]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/schemajava
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/schemajava/*.java $@
	@cp $(PFX)parser/schemajava/Token.java.source $(GENERATED_SRC_PATH)$(PFX)parser/schemajava/Token.java	
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/schemajava $< 

$(PROOFJAVA_PARSER) \
	: $(PFX)parser/proofjava/ProofJavaParser.jj
	@echo [create parser for extended java in proofs]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/proofjava
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/proofjava/*.java $@
	@cp $(PFX)parser/proofjava/Token.java.source $(GENERATED_SRC_PATH)$(PFX)parser/proofjava/Token.java
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/proofjava $< 

$(DIFF_PARSER) \
	: $(PFX)parser/diffparser/DiffParser.jj
	@echo [creating unified diff parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/diffparser
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/diffparser/*.java $@
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/diffparser $< 

$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexer.java \
$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexerTokenTypes.java \
	: $(PFX)parser/lexer.g
	@echo [creating KeYLexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser
	@$(ANTLR)  -o $(GENERATED_SRC_PATH)$(PFX)parser $<

$(GENERATED_SRC_PATH)$(PFX)parser/KeYParser.java \
	: $(PFX)parser/keyparser.g \
	  $(GENERATED_SRC_PATH)$(PFX)parser/KeYLexerTokenTypes.txt
	@echo [creating global KeY parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser
	@$(ANTLR) -glib $(PFX)parser/lexer.g \
			 -o $(GENERATED_SRC_PATH)$(PFX)parser $<


$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexer.java \
$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexerTokenTypes.java \
	: $(PFX)parser/simplify/lexer.g
	@echo [creating SimplifyLexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/simplify
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -o $(GENERATED_SRC_PATH)$(PFX)parser/simplify $<

$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyParser.java \
	: $(PFX)parser/simplify/simplify.g \
	  $(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexerTokenTypes.txt
	@echo [creating Simplify parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/simplify
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -glib $(PFX)parser/simplify/lexer.g \
			 -o $(GENERATED_SRC_PATH)$(PFX)parser/simplify $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexer.java \
$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexerTokenTypes.java \
	: $(PFX)speclang/jml/pretranslation/jmlprelexer.g
	@echo [creating JML pre lexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -o $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreParser.java \
	: $(PFX)speclang/jml/pretranslation/jmlpreparser.g \
	  $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation/KeYJMLPreLexerTokenTypes.txt
	@echo [creating JML pre parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -glib $(PFX)speclang/jml/pretranslation/jmlprelexer.g \
			 -o $(GENERATED_SRC_PATH)$(PFX)speclang/jml/pretranslation $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexer.java \
$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexerTokenTypes.java \
	: $(PFX)speclang/jml/translation/jmllexer.g
	@echo [creating JML lexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -o $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation $<

$(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLParser.java \
	: $(PFX)speclang/jml/translation/jmlparser.g \
	  $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation/KeYJMLLexerTokenTypes.txt
	@echo [creating JML parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -glib $(PFX)speclang/jml/translation/jmllexer.g \
	                 -o $(GENERATED_SRC_PATH)$(PFX)speclang/jml/translation $<

$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocLexer.java \
$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocLexerTokenTypes.java \
	: $(PFX)util/keydoc/parser/KeYDocLexer.g
	@echo [creating KeYDoc Lexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser
	@$(ANTLR)  -o $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser $<

$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocParser.java \
$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocParserTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocParserTokenTypes.java \
	: $(PFX)util/keydoc/parser/KeYDocParser.g \
	  $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocLexerTokenTypes.txt 
	@echo [creating KeYDoc Parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser
	@$(ANTLR)  -glib $(PFX)util/keydoc/parser/KeYDocLexer.g -o $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser $<

$(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocTreeWalker.java \
	: $(PFX)util/keydoc/parser/KeYDocTreeWalker.g \
	  $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser/KeYDocParserTokenTypes.txt 
	@echo [creating KeYDoc Treewalker]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser
	@$(ANTLR)  -glib $(PFX)util/keydoc/parser/KeYDocParser.g -o $(GENERATED_SRC_PATH)$(PFX)util/keydoc/parser $<



$(BINARYPATH)$(PFX)util/make/MakefileReader.class:
	@mkdir -p $(GENERATED_SRC_PATH)
	@mkdir -p $(BINARYPATH)$(PFX)util/make/
	@$(JAVAC) $(OPTIONS) $(PFX)util/make/MakefileReader.java  2>&1 


$(BINARYPATH)$(PFX)util/make/GenericParser.class: $(BINARYPATH)$(PFX)util/make/MakefileReader.class
	@mkdir -p $(BINARYPATH)$(PFX)util/make/
	@$(JAVAC) $(OPTIONS) $(PFX)util/make/GenericParser.java 2>&1 

genericMakefile: $(BINARYPATH)$(PFX)util/make/GenericParser.class
	@$(JAVA) -cp $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH) de.uka.ilkd.key.util.make.GenericParser $(GENERATED_SRC_PATH) GenMakefile argfile.generic $(JAVAFILES)


GenMakefile:;

sinclude GenMakefile

%.java: $(BINARYPATH)$(PFX)util/make/GenericParser.class
	@$(JAVA) -cp $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH) de.uka.ilkd.key.util.make.GenericParser $(GENERATED_SRC_PATH) GenMakefile argfile.generic $(JAVAFILES)
	@$(MAKE) -s -w -f GenMakefile $@ >msg.txt


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
