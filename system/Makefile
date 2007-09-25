# This file is part of KeY - Integrated Deductive Software Design 
# Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
#                         Universitaet Koblenz-Landau, Germany
#                         Chalmers University of Technology, Sweden 
#
# The KeY system is protected by the GNU General Public License. 
# See LICENSE.TXT for details.

#$Format: "PRCSVERSION = \"$ProjectVersion$\""$ 
PRCSVERSION = "hoareWithUpdates.17"

SHELL=/bin/sh
#comon prefix
PFX=de/uka/ilkd/key/


#
#the path where to put the binaries.  This should be different from
#the source path (.), otherwise `make clean' will delete the 
#source tree.
BINARYPATH=binary/

# generated source path
GENERATED_SRC_PATH=genSrc/

#the path where the resources are put (images etc.)
RESOURCEPATH=./resources/
#the path where the GF grammars are
GFGRAMMARPATH=de/uka/ilkd/key/ocl/gf/grammars2
GRAMMARLIST=$(BINARYPATH)$(GFGRAMMARPATH)/grammars2list.txt

#include configuration information
sinclude ./Makefile.mk

ifeq "$(JAVA)" ""
JAVA=$(shell which java)
endif

JIKESPATH=$(CLASSPATH):$(GENERATED_SRC_PATH):$(JAVA_HOME)/jre/lib/rt.jar

# enables optimization and removes debug info (such as line tables)
#COMMON_OPTIONS=-O -g:none -d $(BINARYPATH)

COMMON_OPTIONS=-g -d $(BINARYPATH) 
OPTIONS=$(COMMON_OPTIONS)


ifeq "$(KEYVERS)" ""
KEYVERS=$(PRCSVERSION)
endif


ifeq "$(JAVAC)" ""
JAVAC=javac
endif

ifeq "$(ANTLR)" ""
ANTLR=$(JAVA) -cp $(GENERATED_SRC_PATH):$(CLASSPATH) antlr.Tool
endif




ifeq ($(JAVAC),jikes) 
VERSION=$(shell jikes -version | grep "Version" )
VERSION:=$(wordlist 5,5,$(VERSION))
OPTIONS=$(COMMON_OPTIONS) +D +E +P -source 1.4 -classpath $(JIKESPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
ifeq ($(VERSION), 1.19)
else 
OPTIONS:=+Peffective-java $(OPTIONS) 
endif 
else
  ifeq ($(JAVAC),ajc)
    OPTIONS=$(COMMON_OPTIONS) -nowarn -classpath $(ASPECTJRTPATH):$(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
  else
    ifeq ($(JAVAC),ejc)      
       OPTIONS=$(COMMON_OPTIONS) -warn:uselessTypeCheck,localHiding,fieldHiding,tasks\(TODO\|HACK\|%%%\)  -source 1.4 -classpath $(JAVA_HOME)/jre/lib/rt.jar:$(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
    else 
      OPTIONS=$(COMMON_OPTIONS) -J-Xmx512m -nowarn -source 1.4 -classpath $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH):.
    endif
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
TOGETHER_ENABLED?=--with-together
export TOGETHER_ENABLED
COMPILE_GF?=--with-gf
export COMPILE_GF

# this part creates .java-files from .gjava files
#	rule/SLListOfRule rule/SLListOfRuleApp \

GENERATED_ITERATORS=proof/IteratorOfNode \
	logic/op/IteratorOfBoolean \
	rule/IteratorOfListOfNoPosTacletApp \
	logic/ldt/IteratorOfLDT \
	java/abstraction/IteratorOfListOfType \
	rule/IteratorOfVariableCondition \
	logic/op/IteratorOfOperator \
	logic/ldt/IteratorOfLDT

GENERATED_LISTS=logic/SLListOfTerm \
	logic/op/SLListOfQuantifiableVariable \
	logic/SLListOfNamed \
	logic/op/SLListOfSchemaVariable \
	rule/SLListOfNewVarcond \
	rule/SLListOfVariableCondition \
	logic/op/SLListOfLogicVariable \
	logic/op/SLListOfParsableVariable \
	logic/op/SLListOfOperator \
	logic/op/SLListOfLocation \
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
        proof/decproc/translation/SLListOfIOperatorTranslation \
	logic/sort/SLListOfGenericSort \
	rule/inst/SLListOfGenericSortCondition \
	logic/op/SLListOfSortDependingSymbol \
	logic/SLListOfName \
	rule/soundness/SLListOfSkolemSet \
	rule/soundness/SLListOfSVTypeInfo \
	logic/op/SLListOfIProgramVariable \
	logic/SLListOfSequentChangeInfo \
	logic/SLListOfFormulaChangeInfo \
	proof/SLListOfTermTacletAppIndex \
	strategy/SLListOfRuleAppContainer \
	rule/updatesimplifier/SLListOfUpdate \
	rule/updatesimplifier/SLListOfAssignmentPair \
	rule/SLListOfIUpdateRule \
	rule/SLListOfUpdatePair \
	logic/SLListOfProgramElementName \
	proof/mgt/SLListOfQuantifierPrefixEntry \
	proof/SLListOfInstantiationProposer \
        speclang/SLListOfOperationContract \
	speclang/SLListOfClassInvariant \
	casetool/SLListOfModelClass \
	casetool/SLListOfModelMethod \
	proof/init/SLListOfProofOblInput \
	logic/op/SLListOfNonRigidFunction \
	rule/export/SLListOfTacletModelInfo \
	rule/export/SLListOfOptionModelInfo \
	rule/export/SLListOfRuleSetModelInfo \
	rule/export/SLListOfDisplayNameModelInfo \
	rule/export/SLListOfCategoryModelInfo \
	logic/SLListOfNamespace \
	casetool/SLListOfAssociation \
	casetool/SLListOfAssociationEnd \
	parser/ocl/SLListOfPropertyResolver \
        parser/ocl/SLListOfOCLEntity \
        rule/encapsulation/SLListOfTypeSchemeTerm \
        rule/encapsulation/SLListOfTypeSchemeConstraint \
	logic/ldt/SLListOfLDT \
        rule/metaconstruct/arith/SLListOfMonomial \
	strategy/feature/instantiator/SLListOfCPBranch \
	strategy/SetAsListOfStrategyFactory \
	visualdebugger/SLListOfLabel \
	pp/SLListOfRange

GENERATED_SETS=logic/SetAsListOfTerm collection/SetAsListOfString \
	rule/SetAsListOfTaclet rule/SetAsListOfRuleApp \
	rule/SetAsListOfNoPosTacletApp \
	logic/op/SetAsListOfQuantifiableVariable \
	logic/op/SetAsListOfSchemaVariable \
	rule/SetAsListOfTacletApp \
	proof/SetAsListOfProof \
	java/SetAsListOfExpression \
	jml/SetAsListOfJMLMethodSpec \
	jml/SetAsListOfSignals \
	logic/op/SetAsListOfProgramVariable \
	logic/op/SetAsListOfProgramMethod \
	logic/sort/SetAsListOfSort \
	logic/sort/SetAsListOfGenericSort \
	logic/op/SetAsListOfIProgramVariable \
	logic/op/SetAsListOfMetavariable \
	logic/SetAsListOfChoice \
	logic/SetAsListOfNamed \
	rule/encapsulation/SetAsListOfTypeScheme \
        rule/encapsulation/SetAsListOfTypeSchemeVariable \
	logic/SetAsListOfLocationDescriptor \
        logic/op/SetAsListOfLogicVariable \
	strategy/quantifierHeuristics/SetAsListOfTrigger\
	strategy/quantifierHeuristics/SetAsListOfSubstitution \
        proof/SetAsListOfGoalChooserBuilder \
	strategy/SetAsListOfStrategyFactory \
	logic/op/SetAsListOfLocation

GENERATED_MAPS=logic/HashMapFromNameToNamed \
	collection/MapAsListFromIntegerToString \
	logic/op/MapAsListFromQuantifiableVariableToInteger \
	logic/op/MapAsListFromSchemaVariableToTerm \
	logic/op/MapAsListFromSchemaVariableToInstantiationEntry \
	logic/op/MapAsListFromLogicVariableToTerm \
	logic/op/MapAsListFromSchemaVariableToTacletPrefix \
	logic/HashMapFromStringToString \
	java/abstraction/HashMapFromStringToListOfType \
        rule/HashMapFromObjectToListOfNoPosTacletApp \
	logic/sort/MapAsListFromGenericSortToSort \
	logic/op/MapAsListFromNameToSortDependingSymbol \
	logic/op/MapAsListFromSchemaVariableToSchemaVariable \
	proof/MapAsListFromConstrainedFormulaToTermTacletAppIndex \
	proof/proofevent/MapAsListFromNodeToNodeChangesHolder \
        logic/HashMapFromNameToInteger \
        logic/HashMapFromIntegerToName \
        logic/op/HashMapFromLogicVariableToSchemaVariable \
	visualdebugger/HashMapFromPosInOccurrenceToLabel \
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
	logic/op/ArrayOfLocationExtnullInnull \
	logic/op/ArrayOfQuantifiableVariableExtnullInnull \
	logic/op/ArrayOfIProgramVariableExtProgramElementInde.uka.ilkd.key.java \
	logic/ArrayOfTermExtnullInnull \
	logic/sort/ArrayOfSortExtnullInnull \
	logic/sort/ArrayOfGenSortExtSortInnull \
	java/abstraction/ArrayOfKeYJavaTypeExtnullInde.uka.ilkd.key.java.abstraction \
	strategy/feature/ArrayOfFeatureExtnullInnull \
	rule/updatesimplifier/ArrayOfAssignmentPairExtnullInnull

GENERATED_HEAPS= logic/LeftistHeapOfInteger \
	strategy/LeftistHeapOfRuleAppContainer

GENERATED_VECTORS_STACKS= rule/VectorOfTaclet \
	util/SimpleStackOfExtList 

GENERATED_COLLECTIONS_ASMKEY = de/uka/ilkd/asmkey/logic/HashMapFromAsmProgramToInteger.java \
	de/uka/ilkd/asmkey/logic/HashMapFromAsmRuleToAsmProgram.java \
	de/uka/ilkd/asmkey/logic/ListOfAsmProgram.java \
	de/uka/ilkd/asmkey/logic/SLListOfAsmProgram.java \
	de/uka/ilkd/asmkey/logic/HashMapFromAsmProgramToListOfAsmProgram.java \
	de/uka/ilkd/asmkey/logic/IteratorOfFormalParameter.java \
	de/uka/ilkd/asmkey/logic/HashMapFromNameToFormalParameter.java \
	de/uka/ilkd/asmkey/logic/IteratorOfDerivedFunction.java \
	de/uka/ilkd/asmkey/logic/sort/ListOfGenericSort.java \
	de/uka/ilkd/asmkey/logic/sort/ListOfAsmSort.java \
	de/uka/ilkd/asmkey/logic/sort/SLListOfGenericSort.java \
	de/uka/ilkd/asmkey/logic/sort/SLListOfAsmSort.java \
	de/uka/ilkd/asmkey/logic/sort/MapFromGenericSortToAsmSort.java \
	de/uka/ilkd/asmkey/logic/sort/MapAsListFromGenericSortToAsmSort.java \
	de/uka/ilkd/asmkey/unit/ListOfImportInfo.java \
	de/uka/ilkd/asmkey/unit/ListOfUnit.java \
	de/uka/ilkd/asmkey/unit/SLListOfUnit.java \
	de/uka/ilkd/asmkey/unit/HashMapFromNameToUnit.java \
	de/uka/ilkd/asmkey/util/graph/IteratorOfEdge.java \
	de/uka/ilkd/asmkey/parser/ast/HashMapFromNameToAstUnit.java \
	de/uka/ilkd/asmkey/parser/ast/IteratorOfAstUnit.java

GEN_FILES=$(GENERATED_MAPS) $(GENERATED_VECTORS_STACKS) $(GENERATED_ARRAYS) $(GENERATED_LISTS) $(GENERATED_SETS) \
	$(GENERATED_ITERATORS) $(GENERATED_HEAPS)

ANTLR_PARSER= \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYLexerTokenTypes.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/KeYParser.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryLexerTokenTypes.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryParser.java \
	$(GENERATED_SRC_PATH)de/uka/ilkd/asmkey/parser/antlr/AsmKeyParser.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/jml/KeYJMLLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/jml/KeYJMLParser.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/simplify/SimplifyParser.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/ocl/KeYOclLexer.java \
	$(GENERATED_SRC_PATH)$(PFX)parser/ocl/KeYOclParser.java \
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
JAVAFILES=$(GEN_FILES:%=$(PFX)%.java) $(GENERATED_COLLECTIONS_ASMKEY)

.PHONY: all
all:	javahomeset
	@$(MAKE) -s all_gen


keybase: TOGETHER_ENABLED=
keybase: COMPILE_GF=
keybase: PLUG_IN_FILTER='\(key/casetool\|key/ocl\|proof/init/OCL\|TestTermParserOCL\|TestTacletParserOCL\|TestOCLTaclets\|TestKey\)'
keybase: javahomeset
	@$(MAKE) -s all_gen



## create javadoc
.PHONY: doc
doc: $(BINARYPATH)$(PFX)util/make/ListJavaFiles.class $(JAVAFILES)
	@mkdir -p doc
## old doc generation	
#	@find de/ | grep "\.java" | grep -v "\~" | xargs javadoc -use -classpath $(CLASSPATH):$(BINARYPATH) -d doc 

## new one produces better output (package index) but is more fragile.
## didn't want to use perl ;)
	@find de/ -name '*.java' | xargs grep -h "^package\|^overview" |\
	cut -d" " -f2 | cut -d";" -f1 | sort | uniq | grep "^de.uka" | \
	xargs $(JAVADOC) $(JAVADOC_OPTIONS) -source 1.4 -classpath $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH) \
	-sourcepath $(GENERATED_SRC_PATH):. -d doc \
	-link http://recoder.sourceforge.net/doc/api \
	-link http://java.sun.com/j2se/1.3/docs/api \
	-link http://www.antlr.org \
	-windowtitle "KeY API Documentation" \
	-doctitle "KeY API Documentation ($(PRCSVERSION))" \
	-header "KeY $(PRCSVERSION)" \
	-private -author -version -J-Xmx256m



## create distribution package
.PHONY: dist
dist:	all
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
	@tar -czvf ../dist/KeY-$(KEYVERS).tgz key.jar setup.jar -C ../ LICENSE.TXT
	@cp ../README.install.bytecode ../dist/README-$(KEYVERS).txt
	@echo "[deleting distribution directory structure]"
	@rm -rf dist

.PHONY: jar
jar:	all
	@echo "[creating jar-file]"
	@jar cfm key.jar resources/MANIFEST.MF -C binary/ .

.PHONY: dist_src
dist_src: distclean
	@rm -rf /tmp/keydist-$(USER)
	@echo "[creating source archive]"
	@mkdir -p /tmp/keydist-$(USER)
	@ln -s $(shell cd ..;pwd) /tmp/keydist-$(USER)/key-$(KEYVERS)
	@tar -C/tmp/keydist-$(USER) --dereference  \
        -cvzf /tmp/keydist-$(USER)/KeY-$(KEYVERS)-src.tgz \
        --exclude=key-$(KEYVERS)/key-ext-jars/'*' --exclude=key-$(KEYVERS)/eclipse/'*'     key-$(KEYVERS)
	@mv /tmp/keydist-$(USER)/KeY-$(KEYVERS)-src.tgz ..
	@cp /tmp/keydist-$(USER)/key-$(KEYVERS)/README.install.source ../README-$(KEYVERS)-src.txt
	@echo "[done]"


.PHONY: clean
## clean
clean:
	@echo [deleting generated .java-files]
	@(cat argfile.generic | xargs -n 1 rm -f )2>error.msg
	@echo [deleting binaries]
	@/bin/rm -rf $(BINARYPATH)
	@/bin/rm -rf $(GENERATED_SRC_PATH)

#help files of the makefile (without the GenMakefile)

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
	@rm -f key.jar
	@rm -f KeY.tgz
	@rm -f keySource.tgz

.PHONY: all_gen
all_gen: genericMakefile
	@$(MAKE) -s all_hlp   	

.PHONY: all_hlp
all_hlp: argfile.normal $(JAVAFILES) $(ANTLR_PARSER) $(JAVACC_PARSER) $(PROOFJAVA_PARSER) $(KEYDOC_JAVAS) $(DIFF_PARSER) copyResources $(GRAMMARLIST)
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

$(GRAMMARLIST):
ifeq ("$(COMPILE_GF)","--with-gf")
	@echo [GF is being compiled]
	@./"${BINARYPATH}/${GFGRAMMARPATH}/compileGrammars.sh" "${BINARYPATH}/${GFGRAMMARPATH}" "${PWD}/../key-ext-jars" > gf.msg
else
	@echo [GF skipped]
endif

argfile.normal: $(BINARYPATH)$(PFX)util/make/ListJavaFiles.class ../key.prj
	@echo [reading project file]
	@$(JAVA) -cp $(CLASSPATH):$(BINARYPATH) de.uka.ilkd.key.util.make.ListJavaFiles <../key.prj >argfile.normal
	@echo "TestKey.java" >> argfile.normal 
## make gjava -> java


$(JAVACC_PARSER) \
	: $(PFX)parser/schemajava/SchemaJavaParser.jj
	@echo [creating parser for schematic java in taclets]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/schemajava
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/schemajava/*.java $@
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/schemajava $< 

$(PROOFJAVA_PARSER) \
	: $(PFX)parser/proofjava/ProofJavaParser.jj
	@echo [create parser for extended java in proofs]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/proofjava
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/proofjava/*.java $@
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/proofjava $< 

$(DIFF_PARSER) \
	: $(PFX)parser/diffparser/DiffParser.jj
	@echo [creating unified diff parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/diffparser
	@rm -f $(GENERATED_SRC_PATH)$(PFX)parser/diffparser/*.java $@
	@$(JAVA) -cp $(CLASSPATH) $(JAVACC_MAIN) -OUTPUT_DIRECTORY=$(GENERATED_SRC_PATH)$(PFX)parser/diffparser $< 

$(BINARYPATH)$(PFX)util/make/ListJavaFiles.class: $(GENERATED_SRC_PATH)$(PFX)util/make/ListJavaFiles.java
	@echo [compile project file reader]
	@$(JAVAC) $(OPTIONS) $< 2>&1 | (grep -v "Caution\|Warning" || true)

$(GENERATED_SRC_PATH)$(PFX)util/make/ListJavaFiles.java: $(PFX)util/make/prcs.g
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)util/make/
	@echo [creating project file reader]
	@$(ANTLR) -o $(GENERATED_SRC_PATH)$(PFX)/util/make $<  


$(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryLexer.java \
$(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryLexerTokenTypes.java \
	: $(PFX)parser/dictionary/dictionaryLexer.g
	@echo [creating DictionaryLexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/dictionary
	@$(ANTLR)  -o $(GENERATED_SRC_PATH)$(PFX)parser/dictionary $<

$(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryParser.java \
	: $(PFX)parser/dictionary/dictionary.g \
	  $(GENERATED_SRC_PATH)$(PFX)parser/dictionary/DictionaryLexerTokenTypes.txt
	@echo [creating dictionary parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/dictionary
	@$(ANTLR)  -glib $(PFX)parser/dictionary/dictionaryLexer.g \
			 -o $(GENERATED_SRC_PATH)$(PFX)parser/dictionary $<

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

$(GENERATED_SRC_PATH)$(PFX)parser/jml/KeYJMLLexer.java \
$(GENERATED_SRC_PATH)$(PFX)parser/jml/KeYJMLLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)parser/jml/KeYJMLLexerTokenTypes.java \
	: $(PFX)parser/jml/lexer.g
	@echo [creating KeYJMLLexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/jml
	@$(ANTLR)  -o $(GENERATED_SRC_PATH)$(PFX)parser/jml $<

$(GENERATED_SRC_PATH)$(PFX)parser/jml/KeYJMLParser.java \
	: $(PFX)parser/jml/jml.g \
	  $(GENERATED_SRC_PATH)$(PFX)parser/jml/KeYJMLLexerTokenTypes.txt
	@echo [creating jml parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/jml
	@$(ANTLR)  -glib $(PFX)parser/jml/lexer.g \
			 -o $(GENERATED_SRC_PATH)$(PFX)parser/jml $<

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

$(GENERATED_SRC_PATH)$(PFX)parser/ocl/KeYOclLexer.java \
$(GENERATED_SRC_PATH)$(PFX)parser/ocl/KeYOclLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)$(PFX)parser/ocl/KeYOclLexerTokenTypes.java \
	: $(PFX)parser/ocl/lexer.g
	@echo [creating KeYOclLexer]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/ocl
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -o $(GENERATED_SRC_PATH)$(PFX)parser/ocl $<

$(GENERATED_SRC_PATH)$(PFX)parser/ocl/KeYOclParser.java \
	: $(PFX)parser/ocl/ocl.g \
	  $(GENERATED_SRC_PATH)$(PFX)parser/ocl/KeYOclLexerTokenTypes.txt
	@echo [creating ocl parser]
	@mkdir -p $(GENERATED_SRC_PATH)$(PFX)parser/ocl
	@$(JAVA) -cp $(CLASSPATH) antlr.Tool  -glib $(PFX)parser/ocl/lexer.g \
			 -o $(GENERATED_SRC_PATH)$(PFX)parser/ocl $<

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
	@$(JAVA) -cp $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH) de.uka.ilkd.key.util.make.GenericParser GenMakefile argfile.generic $(JAVAFILES)


GenMakefile:;

sinclude GenMakefile

%.java: $(BINARYPATH)$(PFX)util/make/GenericParser.class
	@$(JAVA) -cp $(CLASSPATH):$(GENERATED_SRC_PATH):$(BINARYPATH) de.uka.ilkd.key.util.make.GenericParser GenMakefile argfile.generic $(JAVAFILES)
	@$(MAKE) -s -w -f GenMakefile $@ >msg.txt


.PHONY: help
help:
	@echo
	@echo " (g)make"
	@echo "    help:      prints this message"
	@echo
	@echo "    all:       compiles the KeY-system and if necessary creates"
	@echo "               a local Together installation (if the "
	@echo "               configuration file config.mk does not exist)"  
	@echo
	@echo "    keybase:   compiles the KeY-system without the together plug-in"  
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
	@./checkEnvironment $(TOGETHER_ENABLED)
	@mkdir -p $(BINARYPATH)


## AsmKey

$(GENERATED_SRC_PATH)de/uka/ilkd/asmkey/parser/antlr/AsmKeyLexer.java \
$(GENERATED_SRC_PATH)de/uka/ilkd/asmkey/parser/antlr/AsmKeyLexerTokenTypes.txt \
$(GENERATED_SRC_PATH)de/uka/ilkd/asmkey/parser/antlr/AsmKeyLexerTokenTypes.java \
	: de/uka/ilkd/asmkey/parser/antlr/AsmKeyLexer.g
	@echo "[creating $(basename $(notdir $@))]"
	@install -d $(dir $@)
	@$(ANTLR) -o $(dir $@) $<

$(GENERATED_SRC_PATH)de/uka/ilkd/asmkey/parser/antlr/AsmKeyParser.java \
	: de/uka/ilkd/asmkey/parser/antlr/AsmKeyParser.g \
	$(GENERATED_SRC_PATH)de/uka/ilkd/asmkey/parser/antlr/AsmKeyLexerTokenTypes.txt
	@echo "[creating $(basename $(notdir $@))]"
	@install -d $(dir $@)
	@$(ANTLR) -o $(dir $@) $<

# eclipse plug-in:
eclipse-plug-in: dist
	cd ../eclipse/KeYFeature && $(MAKE)
	@rm -fr $(BINARYPATH)$(PFX)casetool/eclipse
	@mkdir -p $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/features
	@mkdir -p $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins
	@cp  ../eclipse/KeYFeature/site.xml $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/ 
	@cp  ../eclipse/KeYFeature/KeY_Feature_*.jar $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/features/
	@cp  ../eclipse/KeYPlugin/KeYPlugin_*.jar $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins/
	@cp  ../eclipse/ProofVisualization/ProofVisualization_*.jar $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins
	@cp  ../eclipse/org.key-project.core/org.key_project.core_* $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins
	@cp  ../eclipse/KeYExternalLibraries/KeYExternalLibraries_1* $(BINARYPATH)$(PFX)casetool/eclipse/KeY_Feature/plugins

