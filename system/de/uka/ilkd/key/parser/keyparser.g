// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/* -*-antlr-*- */
header {

  package de.uka.ilkd.key.parser;

  import antlr.*;

  import java.io.*;
  import java.util.List;
  import java.util.Iterator;
  import java.util.ArrayList;
  import java.util.LinkedList;
  import java.util.HashMap;
  import java.util.HashSet;
  import java.util.Vector;
  import java.math.BigInteger;

  import de.uka.ilkd.key.collection.ListOfString;
  import de.uka.ilkd.key.collection.IteratorOfString;
  import de.uka.ilkd.key.collection.SLListOfString;

  import de.uka.ilkd.key.logic.*;
  import de.uka.ilkd.key.logic.op.*;
  import de.uka.ilkd.key.logic.sort.*;
  import de.uka.ilkd.key.logic.sort.oclsort.OclSort;

  import de.uka.ilkd.key.proof.*;
  import de.uka.ilkd.key.proof.init.*;

  import de.uka.ilkd.key.rule.*;
  import de.uka.ilkd.key.rule.conditions.*;
  import de.uka.ilkd.key.rule.metaconstruct.*;
 
  import de.uka.ilkd.key.speclang.SetAsListOfOperationContract;
  import de.uka.ilkd.key.speclang.SetOfOperationContract;
  import de.uka.ilkd.key.speclang.dl.translation.DLSpecFactory;

  import de.uka.ilkd.key.util.*;

  import de.uka.ilkd.key.java.JavaInfo;
  import de.uka.ilkd.key.java.Services;
  import de.uka.ilkd.key.java.JavaReader;
  import de.uka.ilkd.key.java.SchemaJavaReader;
  import de.uka.ilkd.key.java.abstraction.*;
  import de.uka.ilkd.key.java.visitor.*;
  import de.uka.ilkd.key.java.Recoder2KeY;
  import de.uka.ilkd.key.java.SchemaRecoder2KeY;
  import de.uka.ilkd.key.java.StatementBlock;
  import de.uka.ilkd.key.java.declaration.VariableDeclaration;
  import de.uka.ilkd.key.java.recoderext.*;
  import de.uka.ilkd.key.pp.AbbrevMap;
  import de.uka.ilkd.key.pp.LogicPrinter;
}

/** 
 * General KeY parser, can work in different modes (parserMode)
 */  
class KeYParser extends Parser;
options {
    importVocab=KeYLexer;
    k = 1;
    defaultErrorHandler=true;
}

{
    static final Sort[] AN_ARRAY_OF_SORTS = new Sort[0];
    static final Term[] AN_ARRAY_OF_TERMS = new Term[0];

    private final static int NORMAL_NONRIGID = 0;
    private final static int LOCATION_MODIFIER = 1;
    private final static int HEAP_DEPENDENT = 2;

    static HashMap prooflabel2tag = new HashMap(15);
    static {
      prooflabel2tag.put("branch", new Character('b'));
      prooflabel2tag.put("rule", new Character('r'));
      prooflabel2tag.put("term", new Character('t'));
      prooflabel2tag.put("formula", new Character('f'));
      prooflabel2tag.put("inst", new Character('i'));
      prooflabel2tag.put("ifseqformula", new Character('q'));
      prooflabel2tag.put("heur", new Character('h'));
      prooflabel2tag.put("builtin", new Character('n'));
      prooflabel2tag.put("keyLog", new Character('l'));
      prooflabel2tag.put("keyUser", new Character('u'));
      prooflabel2tag.put("keyVersion", new Character('v'));
      prooflabel2tag.put("keySettings", new Character('s'));
      prooflabel2tag.put("contract", new Character('c'));	
      prooflabel2tag.put("userinteraction", new Character('a'));
   }

    private NamespaceSet nss;
    private Choice defaultChoice = null;
    private HashMap category2Default = new HashMap();
    private boolean onlyWith=false;
    private SetOfChoice activatedChoices = SetAsListOfChoice.EMPTY_SET;
    private SetOfChoice selectedChoices = SetAsListOfChoice.EMPTY_SET;
    private HashSet usedChoiceCategories = new HashSet();
    private HashMap taclet2Builder;
    private AbbrevMap scm;
    private KeYExceptionHandler keh = null;

    // these variables are set if a file is read in step by
    // step. This used when reading in LDTs because of cyclic
    // dependencies.
    private boolean skip_schemavariables;
    private boolean skip_functions;
    private boolean skip_predicates;
    private boolean skip_sorts;
    private boolean skip_rulesets;
    private boolean skip_taclets;
    private boolean parse_includes = false;
    private Includes includes = new Includes();

    private boolean schemaMode = false;
    private ParserMode parserMode;

    private boolean chooseContract = false;
    private int savedGuessing = -1;

    private int lineOffset=0;
    private int colOffset=0;
    private int stringLiteralLine=0; // HACK!

    private Services services;
    private TermFactory tf;
    private JavaReader javaReader;

    // if this is used then we can capture parts of the input for later use
    private DeclPicker capturer = null;
    private ProgramMethod pm = null;

    private SetOfTaclet taclets = SetAsListOfTaclet.EMPTY_SET; 
    private SetOfOperationContract contracts = SetAsListOfOperationContract.EMPTY_SET;

    private ParserConfig schemaConfig;
    private ParserConfig normalConfig;
    
    // the current active config
    private ParserConfig parserConfig;

    private Term quantifiedArrayGuard = null;
    private boolean parsingContracts = false;
    private boolean parsingFind      = false;
    
    private TokenStreamSelector selector;

    /**
     * Although the parser mode can be deduced from the particular constructor
     * used we still require the caller to provide the parser mode explicitly, 
     * so that the code is readable.
     */
    public KeYParser(ParserMode mode, TokenStream lexer) {
	this((lexer instanceof KeYLexer)? ((KeYLexer)lexer).getSelector() : ((DeclPicker)lexer).getSelector(), 2);
        this.selector = (lexer instanceof KeYLexer)? ((KeYLexer)lexer).getSelector() : ((DeclPicker)lexer).getSelector();
	this.parserMode = mode;
    }

    public KeYParser(ParserMode mode, TokenStream lexer, Services services) {
        this(mode, lexer);
        this.keh = services.getExceptionHandler();
    }

    /* Most general constructor, should only be used internally */
    private KeYParser(TokenStream lexer,
		     String filename,
                     Services services,
		     NamespaceSet nss,
		     TermFactory tf,
		     ParserMode mode) {
        this(mode, lexer);
        setFilename(filename);
 	this.services = services;
	if(services != null)
          this.keh = services.getExceptionHandler();
	this.nss = nss;
	
        this.defaultChoice = new Choice(new Name("Default"));
        if(nss != null) {
            this.defaultChoice.setFuncNS(nss.functions());
        }
                
	this.tf = tf;
        switchToNormalMode();
    }

    /** 
     * Used to construct Declaration parser - for signature declarations,
     * i.e. sorts, schema variabls, predicates, functions and rule sets.
     */  
    public KeYParser(ParserMode mode, TokenStream lexer,
                     String filename, Services services,
                     NamespaceSet nss) {
        this(lexer, filename, services, nss, null, mode);
	resetSkips();
    }


    /** 
     * Used to construct Term parser - for first-order terms
     * and formulae.
     */  
    public KeYParser(ParserMode mode, TokenStream lexer,                   
                     String filename, TermFactory  tf,
                     JavaReader jr, Services services,
                     NamespaceSet nss, AbbrevMap scm) {
        this(lexer, filename, services, nss, tf, mode);
        this.javaReader = jr;
        this.scm = scm;
    }


    /** ONLY FOR TEST CASES.
     * Used to construct Global Declaration Term parser - for first-order 
     * terms and formulae. Variables in quantifiers are expected to be
     * declared globally in the variable namespace.  This parser is used
     * for test cases, where you want to know in advance which objects
     * will represent bound variables.
     */  
    public KeYParser(ParserMode mode, TokenStream lexer,
		     TermFactory tf, JavaReader jr,
		     NamespaceSet nss) {
        this(lexer, null, new Services(), nss, tf, mode);
        this.scm = new AbbrevMap();
        this.javaReader = jr;
    }

    public KeYParser(ParserMode mode, TokenStream lexer,
		     TermFactory tf, Services services,
		     NamespaceSet nss) {
	this(mode, lexer, tf, 
	     new Recoder2KeY(
		new KeYCrossReferenceServiceConfiguration(
		   services.getExceptionHandler()), 
		services.getJavaInfo().rec2key(), new NamespaceSet(), 
		services.getTypeConverter()),
   	     nss);
    }

    public KeYParser(ParserMode mode, TokenStream lexer,
		     Services services, NamespaceSet nss) {
	this(mode, lexer, TermFactory.DEFAULT,
	     new Recoder2KeY(
	       new KeYCrossReferenceServiceConfiguration(
	         services.getExceptionHandler()),
	       services.getJavaInfo().rec2key(), new NamespaceSet(),
	       services.getTypeConverter()),
	     nss);
    }


    /**
     * Used to construct Taclet parser
     */  
    public KeYParser(ParserMode mode, TokenStream lexer,
                     String filename, TermFactory tf,
                     SchemaJavaReader jr, Services services,  
                     NamespaceSet nss, HashMap taclet2Builder) {
        this(lexer, filename, services, nss, tf, mode);
        switchToSchemaMode();
        this.scm = new AbbrevMap();
        this.javaReader = jr;
        this.taclet2Builder = taclet2Builder;
    }

    public KeYParser(ParserMode mode, TokenStream lexer,
                     String filename, TermFactory tf,
                     Services services, NamespaceSet nss) {
        this(mode, lexer, filename, tf,
             new SchemaRecoder2KeY(services, nss),
	     services, nss, new HashMap());
    }


    /** 
     * Used to construct Problem parser
     */  
    public KeYParser(ParserMode mode, TokenStream lexer, 
                     String filename, ParserConfig schemaConfig,
                     ParserConfig normalConfig, HashMap taclet2Builder,
                     SetOfTaclet taclets, SetOfChoice selectedChoices) { 
        this(lexer, filename, null, null, null, mode);
        if (lexer instanceof DeclPicker) {
            this.capturer = (DeclPicker) lexer;
        }
        if (normalConfig!=null)
        scm = new AbbrevMap();
        tf = TermFactory.DEFAULT;
        this.schemaConfig = schemaConfig;
        this.normalConfig = normalConfig;       
	switchToNormalMode();
        this.taclet2Builder = taclet2Builder;
        this.taclets = taclets;
	if(selectedChoices != null)
	   this.selectedChoices = selectedChoices;
        if(normalConfig != null){
            this.keh = normalConfig.services().getExceptionHandler();
           	this.defaultChoice.setFuncNS(parserConfig.namespaces().functions());
        }else{
            this.keh = new KeYRecoderExcHandler();
        }
    }

    public KeYParser(ParserMode mode, TokenStream lexer, String filename) { 
        this(lexer, filename, null, null, null, mode);
        if (lexer instanceof DeclPicker) {
            this.capturer = (DeclPicker) lexer;
        }
        scm = new AbbrevMap();
        tf = TermFactory.DEFAULT;
        this.schemaConfig = null;
        this.normalConfig = null;       
	switchToNormalMode();
        this.taclet2Builder = null;
        this.taclets = null;
        this.keh = new KeYRecoderExcHandler();
    }
 
    public boolean getChooseContract() {
      return chooseContract;
    }
    
    public String getFilename() {
      return ((CharScanner)selector.getCurrentStream()).getFilename();
    }

    public void setFilename(String filename) {
      ((CharScanner)selector.getCurrentStream()).setFilename(filename);
    }
 
    private boolean isDeclParser() {
	return parserMode == ParserMode.DECLARATION;
    }

    private boolean isTermParser() {
	return parserMode == ParserMode.TERM;
    }

    private boolean isGlobalDeclTermParser() {
	return parserMode == ParserMode.GLOBALDECL;
    }

    private boolean isTacletParser() {
	return parserMode == ParserMode.TACLET;
    }

    private boolean isProblemParser() {
	return parserMode == ParserMode.PROBLEM;
    }

    public void reportError(RecognitionException ex){
        keh.reportException(ex);
    }

    public SetOfChoice getActivatedChoices(){
        return activatedChoices;
    }
    
    public Includes getIncludes(){
        return includes;
    }

    public JavaInfo getJavaInfo() {
        if(isProblemParser()) 
          return parserConfig.javaInfo();
    	if(getServices() != null)
          return getServices().getJavaInfo();
	else
	  return null;
    }

    public Services getServices() {
        if(isProblemParser()) 
          return parserConfig.services();
        return services;
    }

    public NamespaceSet namespaces() {
        if(isProblemParser()) 
          return parserConfig.namespaces();
        return nss;
    }

    public Namespace sorts() {
        return namespaces().sorts();
    }

    public Namespace functions() {
        return namespaces().functions();
    }

    public Namespace ruleSets() {
        return namespaces().ruleSets();
    }

    public Namespace variables() {
        return namespaces().variables();
    }

    public Namespace programVariables() {
        return namespaces().programVariables();
    }

    public Namespace choices(){
        return namespaces().choices();
    }

    public SetOfTaclet getTaclets(){
        return taclets;
    }

    public SetOfOperationContract getContracts(){
        return contracts;
    }
    
    public HashMap getCategory2Default(){
        return category2Default;
    }

    private boolean inSchemaMode() {
	if(isTermParser() && schemaMode)
	   Debug.fail("In Term parser mode schemaMode cannot be true.");
	if(isTacletParser() && !schemaMode)
	   Debug.fail("In Taclet parser mode schemaMode should always be true.");
        return schemaMode;
    }

    private void switchToSchemaMode() {
	if(!isTermParser()) {
          schemaMode = true;
	  if(isProblemParser())
            parserConfig = schemaConfig;    
	}
    }

    private void switchToNormalMode() {
	if(!isTermParser() && !isTacletParser()) {
          schemaMode = false;      
	  if(isProblemParser())
            parserConfig = normalConfig;
	}
    }

    private int getLine() {
        int line = -1;
        try {
            line = LT(0).getLine() + lineOffset;
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return line;
    }   

    private int getColumn() {
        int col = -1;
        try {
            col = LT(0).getColumn() + colOffset;
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return col;
    }   

    private void resetSkips() {
       skip_schemavariables = false;
       skip_functions       = false;
       skip_predicates      = false;
       skip_sorts           = false;
       skip_rulesets        = false;
       skip_taclets         = false;
    }

    private void skipFuncs() {
        skip_functions = true;
    }
    
    private void skipPreds() {
        skip_predicates = true;
    }

    private void skipTaclets() {
        skip_taclets = true;
    }

    private void skipVars() {
        skip_schemavariables = true;
    }

    private void skipSorts() {
        skip_sorts = true;
    }

    private void skipRuleSets() {
        skip_rulesets = true;
    }
    
    private Named lookup(Name n) {
       if(isProblemParser()) {
          final Namespace[] lookups = {
            normalConfig.namespaces().functions(), 
            schemaConfig.namespaces().functions(), 
            normalConfig.namespaces().variables(), 
            schemaConfig.namespaces().variables(), 
            schemaConfig.namespaces().programVariables()
          };
          return doLookup(n,lookups);
       } else {
          final Namespace[] lookups = {
              functions(), variables(), 
              programVariables()
          };
          return doLookup(n,lookups);
       }
    }

    private static Named doLookup(Name n, Namespace[] lookups) {
        for (int i = 0; i<lookups.length; i++) {
            if (lookups[i].lookup(n) != null) {
                return lookups[i].lookup(n);
            }
        }
        return null;    
    }

    private void addInclude(String filename, boolean relativePath, boolean ldt){
        RuleSource source=null;
        if (relativePath) {
            int end = getFilename().lastIndexOf(File.separator);
            int start = 0;
            filename = filename.replace('/', File.separatorChar);
            filename = filename.replace('\\', File.separatorChar);
            if(getFilename().startsWith("file:")){
                start = 5;
            }
            File path=new File(getFilename().substring(start,end+1)+filename);
            try{ 
                source = RuleSource.initRuleFile(path.toURL()); 
            }catch(java.net.MalformedURLException e){
                System.err.println("Exception due to malformed URL of file "+
                                   filename+"\n " +e);
            }
        } else {
            source = RuleSource.initRuleFile(filename+".key"); 
        }
        if (ldt) {
            includes.putLDT(filename, source);
        } else {
            includes.put(filename, source);
        }
    }  

    public void parseVariables()
        throws RecognitionException, TokenStreamException {
      resetSkips();
      skipFuncs(); skipPreds(); skipSorts(); skipRuleSets();
      decls();
      resetSkips();
    }

    public void parseFunctions()
        throws RecognitionException, TokenStreamException {
      resetSkips();
      skipVars(); skipPreds(); skipSorts(); skipRuleSets();
      decls();
      resetSkips();
    }

    public void parsePredicates()
        throws RecognitionException, TokenStreamException {
      resetSkips();
      skipVars(); skipFuncs(); skipSorts(); skipRuleSets();
      decls();
      resetSkips();
    }

    public void parseSorts() 
        throws RecognitionException, TokenStreamException {
      resetSkips();
      skipVars(); skipFuncs(); skipPreds(); skipRuleSets();
      decls();
      resetSkips();
    }

    public void parseRuleSets()
        throws RecognitionException, TokenStreamException {
      resetSkips();
      skipVars(); skipFuncs(); skipPreds(); skipSorts();
      decls();
      resetSkips();
    }

    public void parseFuncAndPred()
        throws RecognitionException, TokenStreamException {
      resetSkips();
      skipVars(); skipSorts(); skipRuleSets();
      decls();
      resetSkips();
    }
  
    /** parses a problem but without reading the declarations of
     * sorts, functions and predicates. These have to be given
     * explicitly.
     * the heuristics of the current problem file will be added 
     */ 
    public Term parseProblem() 
        throws RecognitionException, TokenStreamException {
      resetSkips();
      skipSorts(); skipFuncs(); skipPreds(); skipTaclets();
      return problem();
    }

    public void parseIncludes()
        throws RecognitionException, TokenStreamException {
      parse_includes=true;
      problem();
    }

    public void parseWith()
        throws RecognitionException, TokenStreamException {
      onlyWith=true;
      problem();
    }

    private void schema_var_decl(String name, Sort s, boolean makeVariableSV,
            boolean makeSkolemTermSV, boolean makeLocationsSV, boolean makeFunctionsSV,
            SchemaVariableModifierSet mods) throws AmbigiousDeclException {
        if (!skip_schemavariables) {

            SchemaVariable v;
            if ( s == Sort.FORMULA ) {
                v = SchemaVariableFactory.createFormulaSV
                (new Name(name), mods.list(), mods.rigid());
            } else if ( s instanceof ProgramSVSort ) {
                v = SchemaVariableFactory.createProgramSV
                (new ProgramElementName(name),(ProgramSVSort) s, mods.list());
            } else {
                if ( makeVariableSV ) {
                    v=SchemaVariableFactory.createVariableSV
                    (new Name(name), s, mods.list());
                } else if ( makeSkolemTermSV ) {
                    v = SchemaVariableFactory.createSkolemTermSV
                    (new Name(name), s, mods.list());
                } else if( makeLocationsSV ) {
                	Debug.assertTrue(mods.list());
	                v = SchemaVariableFactory.createListSV(new Name(name), LocationDescriptor.class);
                } else if( makeFunctionsSV ) {
                	Debug.assertTrue(mods.list());
	                v = SchemaVariableFactory.createListSV(new Name(name), Function.class);
                } else { v = SchemaVariableFactory.createTermSV
                    (new Name(name), s, mods.list(), mods.rigid(), mods.strict());
                }
            }          

            if (inSchemaMode()) {
               if (variables().lookup(v.name()) != null) {
            	 throw new AmbigiousDeclException(v.name().toString(), getFilename(), 
            	  				 getLine(), getColumn());
               }
               variables().add(v);
            }
        }
        
    }

    public static Term toZNotation(String number, Namespace functions, TermFactory tf){
	String s = number;
        final boolean negative = (s.charAt(0) == '-');
	if (negative) {
	    s = number.substring(1, s.length());
	}
        if(s.startsWith("0x")) {
	  try {
	    BigInteger bi = new BigInteger(s.substring(2),16);
	    s = bi.toString();
	  } catch(NumberFormatException nfe) {
	    Debug.fail("Not a hexadecimal constant (BTW, this should not have happened).");
	  }
	}
        Term result = tf.createFunctionTerm((Function) functions.lookup(new Name("#")));

        for(int i = 0; i<s.length(); i++){
            result = tf.createFunctionTerm((Function)functions.lookup
                 (new Name(s.substring(i,i+1))), result);
        }

       	if (negative) {
  	    result = tf.createFunctionTerm
		((Function) functions.lookup(new Name("neglit")), result);
        }
	return tf.createFunctionTerm
            ((Function) functions.lookup(new Name("Z")), result); 
    }

    private String getTypeList(ListOfProgramVariable vars) {
	StringBuffer result = new StringBuffer("");
	final IteratorOfProgramVariable it = vars.iterator();
	while (it.hasNext()) {
         result.append(it.next().getContainerType().getFullName());
         if (it.hasNext()) result.append(", ");         
	}
	return result.toString();
    }

    private TermSymbol getAttribute(Sort prefixSort, String attributeName) 
           throws SemanticException {
        final JavaInfo javaInfo = getJavaInfo();
        TermSymbol result = null;

        if (!inSchemaMode()) {
            if (attributeName.indexOf(':') != -1) {     
                result = javaInfo.getAttribute(attributeName);
            } else {
                final KeYJavaType prefixKJT = javaInfo.getKeYJavaType(prefixSort);
                if (prefixKJT == null) {
                    semanticError("Could not find type '"+prefixSort+"'. Maybe mispelled or "+
                        "you use an array or object type in a .key-file with missing " + 
                        "\\javaSource section.");
                }
                // WATCHOUT why not in DECLARATION MODE	   
                if(!isDeclParser()) {			      	
                    if (prefixSort == Sort.NULL) {
                        semanticError
                        ("Cannot uniquely determine attribute " + attributeName + 
                            "\n Please specify exact type by attaching" +
                            " @( delaredInType ) to the attribute name.");
                    }

                    final ListOfProgramVariable vars = 	
                    javaInfo.getAllAttributes(attributeName, prefixKJT);
                    
                    if (vars.size() == 0) {
                        semanticError("There is no attribute '" + attributeName + 
                            "' declared in type '" + prefixSort + "'");
                    }                    

                    if (LogicPrinter.printInShortForm(attributeName, 
                            prefixSort, getServices())) {       		   
                        result = vars.head();
                    } else {
                        if (vars.size() > 1) {
                            semanticError
                            ("Cannot uniquely determine attribute " + attributeName + 
                                "\n Please specify the exact type by attaching" +
                                " @( declaredInType ) to the attribute name." + 
                                "\n Found attributes of the same name in: " + getTypeList(vars));
                        }
                    }
                }              
            }
        }else{
            result = (SortedSchemaVariable)variables().lookup(new Name(attributeName));
        }
        if ( result == null && !("length".equals(attributeName)) ) {
            throw new NotDeclException ("Attribute ", attributeName,
                getFilename(), getLine(), getColumn());
        }
        return result;
    }

   
    public Term createAttributeTerm(Term prefix, TermSymbol attribute,
              Term shadowNumber) {
        Term result = prefix;
	if (!inSchemaMode()) {
          if (((ProgramVariable)attribute).isStatic()){
              result = tf.createVariableTerm((ProgramVariable)attribute);
          } else {
              if (shadowNumber != null) {
                  result = tf.createShadowAttributeTerm((ProgramVariable)attribute, 
                                                        result, shadowNumber);
              } else {
                  result = tf.createAttributeTerm((ProgramVariable)attribute, result);
              }
          }
	} else {
        if (shadowNumber != null) {
                result = tf.createShadowAttributeTerm((SchemaVariable)attribute, result, shadowNumber);
	    } else
                result = tf.createAttributeTerm((SchemaVariable)attribute, result);         
	}
        return result;
    }

    public de.uka.ilkd.key.logic.op.Location[] extractLocations(List /*String, KeYJavaType*/ locNames)
    throws SemanticException {
        de.uka.ilkd.key.logic.op.Location[] vars = 
	    new de.uka.ilkd.key.logic.op.Location[locNames.size()];
        for (int i = 0; i<vars.length; i++) {
            final String strLocName;
            if(locNames.get(i) instanceof KeYJavaType) { //array op
            	strLocName = "[](" + ((KeYJavaType)(locNames.get(i))).getSort().name() + ")";
            } else {
	            strLocName = (String)locNames.get(i);
            }
            final Name locName = new Name(strLocName);
            if(isProblemParser()) {
               vars[i] = (SortedSchemaVariable)
                   schemaConfig.namespaces().variables().lookup(locName);
            }
            if ((vars[i] == null && isProblemParser()) || !isProblemParser()) {
                if(locNames.get(i) instanceof KeYJavaType) { //array op
                    Sort componentSort 
                    		= ((KeYJavaType)(locNames.get(i))).getSort();
                    Sort objectSort 
                    		= getJavaInfo().getJavaLangObjectAsSort();
                    Sort cloneableSort 
                    		= getJavaInfo().getJavaLangCloneableAsSort();
                    Sort serializableSort 
                    		= getJavaInfo().getJavaIoSerializableAsSort();
                    Sort arraySort 
                    	= ArraySortImpl.getArraySort(componentSort,
                    								 objectSort,
                                                     cloneableSort,
                                                     serializableSort);
                    vars[i] = ArrayOp.getArrayOp(arraySort);
                } else {
                    Object o = programVariables().lookup(locName);
                    if (o != null) {
                        vars[i] = (de.uka.ilkd.key.logic.op.Location) o;
                    } else {
                        vars[i] = (de.uka.ilkd.key.logic.op.Location) getAttribute(null, strLocName);
                    }
                }
            }
        }
        return vars;
    }

    public List /*ArrayOfLocation*/ extractPartitionedLocations(List /*List (String, KeYJavaType)*/ locListList)
    throws SemanticException {
        List result = new ArrayList();
        Iterator it = locListList.iterator();
        while(it.hasNext()) {
            List locNames = (List) it.next();
            de.uka.ilkd.key.logic.op.Location[] locs
                        = extractLocations(locNames);
            result.add(new de.uka.ilkd.key.logic.op.ArrayOfLocation(locs));
        }
        return result;
    }

    public static String createDependencyName(String name, List dependencyListList) {
	StringBuffer result = new StringBuffer(name);
        result.append("[");
        Iterator it = dependencyListList.iterator();
        while (it.hasNext()) {
            List dependencyList = (List) it.next();
		    Iterator it2 = dependencyList.iterator();
            while (it2.hasNext()) {
            	Object dep = it2.next();
            	if(dep instanceof KeYJavaType) { //array op
            		result.append("[](" + ((KeYJavaType)dep).getSort().name() + ")");
            	} else {
		        	result.append((String) dep);
            	}
                result.append(";");
	    	}
        	if (it.hasNext()) {
                result.append("|");
            }
        }
        result.append("]");
        
	return result.toString();
    }
     
    private LogicVariable bindVar(String id, Sort s) {
        if(isGlobalDeclTermParser())
  	  Debug.fail("bindVar was called in Global Declaration Term parser.");
        LogicVariable v=new LogicVariable(new Name(id), s);
        namespaces().setVariables(variables().extended(v));
        return v;
    }

    private void bindVar(LogicVariable v) {
        if(isGlobalDeclTermParser())
  	  Debug.fail("bindVar was called in Global Declaration Term parser.");
        namespaces().setVariables(variables().extended(v));
    }

    private void bindVar() {
        if(isGlobalDeclTermParser())
  	  Debug.fail("bindVar was called in Global Declaration Term parser.");
        namespaces().setVariables ( new Namespace ( variables () ) );
    }

  private KeYJavaType getTypeByClassName(String s) 
    throws KeYSemanticException {
        KeYJavaType kjt = null;              
        try {
            final Sort sort = lookupSort(s);
            if (sort != null) {
                kjt=getJavaInfo().getKeYJavaType(sort);
            }
        } catch(RuntimeException e){
            return null;
        }

        return kjt;
    }
    
    private boolean isPackage(String name){
        try {   
            return getJavaInfo().isPackage(name);
        } catch(RuntimeException e){        
            // may be thrown in cases of invalid java identifiers
            return false;
        } 
    }
    
    private void unbindVars() {
        if(isGlobalDeclTermParser()) {
            Debug.fail("unbindVars was called in Global Declaration Term parser.");
        }
        namespaces().setVariables(variables().parent());
    }

    private void bindProgVars(HashSet progVars) {
	namespaces().setProgramVariables(new Namespace(programVariables()));
	Iterator it=progVars.iterator();
	while (it.hasNext()) {
  	      programVariables().add((Named)it.next());
	}
    }

    private void unbindProgVars() {
	if(isGlobalDeclTermParser()) {
   	   namespaces().setVariables(variables().parent());
	} else
	   if(!isDeclParser()) {
             namespaces().setProgramVariables(programVariables().parent());
        }
    }

    private HashSet progVars(JavaBlock jb) {
	if(isGlobalDeclTermParser()) {
  	  ProgramVariableCollector pvc
	      = new ProgramVariableCollector(jb.program(), getServices());
          pvc.start();
          return pvc.result();
        }else 
  	  if(!isDeclParser()) {
            if ((isTermParser() || isProblemParser()) && jb==JavaBlock.EMPTY_JAVABLOCK) {
              return new HashSet();
            }   
            DeclarationProgramVariableCollector pvc
               = new DeclarationProgramVariableCollector(jb.program(), getServices());
            pvc.start();
            return pvc.result();
          }
	Debug.fail("KeYParser.progVars(): this statement should not be reachable.");
	return null;
    }

    private Term termForParsedVariable(ParsableVariable v) 
        throws antlr.SemanticException {
        if ( v instanceof LogicVariable ) {
            return tf.createVariableTerm((LogicVariable)v);
        } else if ( v instanceof ProgramVariable ) {
            return tf.createVariableTerm((ProgramVariable)v);
        } else {
	  if(isGlobalDeclTermParser())
		semanticError(v + " is not a logic variable");
          if ((!isProblemParser()) && (v instanceof Metavariable)) {
             return tf.createFunctionTerm((Metavariable)v);
          } else {
  	     if(isTermParser())
               semanticError(v + " is an unknown kind of variable.");
	    if (inSchemaMode() && v instanceof SchemaVariable ) {
               return tf.createVariableTerm((SchemaVariable)v);
            } else {
	    	String errorMessage = "";
                if ( inSchemaMode() ) {
       	          errorMessage += v +" is not a program, logic or schema variable";
                } else {
                  errorMessage += v +" is not a logic or program variable";
                }
                semanticError(errorMessage);
            }
	  }
	}
	return null;
    }
    
    private PairOfStringAndJavaBlock getJavaBlock(Token t) throws antlr.SemanticException {
	PairOfStringAndJavaBlock sjb = new PairOfStringAndJavaBlock();
        String s=t.getText();
	int index = s.indexOf("\n");
	sjb.opName = s.substring(0,index);
	s = s.substring(index+1);
	Debug.out("Modal operator name passed to getJavaBlock: ",sjb.opName);
	Debug.out("Java block passed to getJavaBlock: ", s);

        JavaReader jr = javaReader;

	try {
            if (inSchemaMode()) {
                if(isProblemParser()) // Alt jr==null;
                jr = new SchemaRecoder2KeY(parserConfig.services(), 
                    parserConfig.namespaces());
                ((SchemaJavaReader)jr).setSVNamespace(variables());
            } else{
                if(isProblemParser()) // Alt jr==null;
                jr = new Recoder2KeY(parserConfig.services(), 
                    parserConfig.namespaces());
            }

            if (inSchemaMode() || isGlobalDeclTermParser()) {
                sjb.javaBlock = jr.readBlockWithEmptyContext(s);
            }else{
                sjb.javaBlock = jr.readBlockWithProgramVariables(programVariables(), s);
            }
        } catch (de.uka.ilkd.key.java.PosConvertException e) {
            lineOffset=e.getLine()-1;
            colOffset=e.getColumn()+1;
            throw new JavaParserException(e, t, 
                getFilename(), lineOffset, colOffset);
        } catch (de.uka.ilkd.key.java.ConvertException e) { 
            if (e.parseException()!=null
            &&  e.parseException().currentToken != null
            &&  e.parseException().currentToken.next != null) {               
                lineOffset=e.parseException().currentToken.next.beginLine;               
                colOffset=e.parseException().currentToken.next.beginColumn;
                e.parseException().currentToken.next.beginLine=getLine()-1;
                e.parseException().currentToken.next.beginColumn=getColumn();
                throw new JavaParserException(e, t, getFilename(), -1, -1);  // row/columns already in text
            }       
            if (e.proofJavaException()!=null
            &&  e.proofJavaException().currentToken != null
            &&  e.proofJavaException().currentToken.next != null) {      
                lineOffset = e.proofJavaException().currentToken.next.beginLine-1;
                colOffset=e.proofJavaException().currentToken.next.beginColumn;
                e.proofJavaException().currentToken.next.beginLine=getLine();
                e.proofJavaException().currentToken.next.beginColumn =getColumn();
                 throw  new JavaParserException(e, t, getFilename(), lineOffset, colOffset); 
                            
            }   
            throw new JavaParserException(e, t, getFilename());
        } 
        return sjb;
    }

    private Operator lookupVarfuncId(String varfunc_name, 
                    PairOfTermArrayAndBoundVarsArray args) throws NotDeclException {
        Term[] argTerms = null;
        if (args != null) {
            argTerms = args.getTerms();
        }
        return lookupVarfuncId(varfunc_name, argTerms);
    }

    /**
     * looks up and returns the sort of the given name or null if none has been found.
     * If the sort is not found for the first time, the name is expanded with "java.lang." 
     * and the look up restarts
     */
     private Sort lookupSort(String name) {        
	Sort result = (Sort) sorts().lookup(new Name(name));
	if (result == null) {
  	    result = (Sort) sorts().lookup(new Name("java.lang."+name));
	}
	return result;
     }
     

    /** looks up a function, (program) variable or static query of the 
     * given name varfunc_id and the argument terms args in the namespaces 
     * and java info. 
     * @param varfunc_name the String with the symbols name
     * @param args is null iff no argument list is given, for instance `f', 
     * and is an array of size zero, if an empty argument list was given,
     * for instance `f()'.
     */
    private Operator lookupVarfuncId(String varfunc_name, Term[] args) 
        throws NotDeclException{
        // case 1: variable
        Operator v = (TermSymbol) variables().lookup(new Name(varfunc_name));
        if (v != null && (args == null || (inSchemaMode() && v instanceof OperatorSV))) {
            return v;
        }
        // case 2: function
        v = (TermSymbol) functions().lookup(new Name(varfunc_name));
        if (v != null) { // we allow both args==null (e.g. `c')
                         // and args.length=0 (e.g. 'c())' here 
            return v;
        }
        // case 3: program variable
        v = (TermSymbol) programVariables().lookup
            (new ProgramElementName(varfunc_name));
        if (v != null && args==null) {
            return v;
        }
        if (args==null) {
            throw new NotDeclException
                ("(program) variable or constant", varfunc_name,
                 getFilename(), getLine(), getColumn());
        } else {
            throw new NotDeclException
                ("function or static query", varfunc_name,
                 getFilename(), getLine(), getColumn());
        }
    }

    private boolean isStaticAttribute() throws KeYSemanticException {	
        if(inSchemaMode()) return false;
        final JavaInfo javaInfo = getJavaInfo();
        KeYJavaType kjt = null;
	boolean result = false;
        try {
            int n = 1; 
            StringBuffer className = new StringBuffer(LT(n).getText());
	    while (isPackage(className.toString()) || LA(n+2)==NUM_LITERAL || 
	    		(LT(n+2)!=null && LT(n+2).getText()!=null && 
	    		LT(n+2).getText().charAt(0)<='Z' && LT(n+2).getText().charAt(0)>='A' && 
	    		(LT(n+2).getText().length()==1 || 
	    		 LT(n+2).getText().charAt(1)<='z' && LT(n+2).getText().charAt(1)>='a'))){  	   
                if (LA(n+1) != DOT && LA(n+1) != EMPTYBRACKETS) return false;
                className.append(".");	       
                className.append(LT(n+2).getText());
                n+=2;
	    }	
        while (LA(n+1) == EMPTYBRACKETS) {
                className.append("[]");
                n++;
        }
	kjt = getTypeByClassName(className.toString());

	    if (kjt != null) { 
		// works as we do not have inner classes
		if (LA(n+1) == DOT) {
		    final ProgramVariable pv = 
		      javaInfo.getAttribute(LT(n+2).getText(), kjt);
		    result = (pv != null && pv.isStatic());		
		}    
	    }else{
	     result = false;
	    }
	} catch (antlr.TokenStreamException tse) {
	    // System.out.println("an exception occured"+tse);
	    result = false;
	}
	if(result && inputState.guessing > 0) {
           savedGuessing = inputState.guessing;
	   inputState.guessing = 0;
	}
	return result;
    }

    private boolean isMetaOperator() throws TokenStreamException {  
    if((LA(1) == IDENT &&
         AbstractMetaOperator.name2metaop(LT(1).getText())!=null)
       || LA(1) == IN_TYPE)
      return true;
    return false;
    }

    private boolean isStaticQuery() throws KeYSemanticException {   
    if(inSchemaMode()) return false;
    final JavaInfo javaInfo = getJavaInfo();
    boolean result = false;
    try {
        int n = 1; 
        KeYJavaType kjt = null;
        StringBuffer className = new StringBuffer(LT(n).getText());
        while (isPackage(className.toString())) {          
          if (LA(n+1) != DOT) return false;
          className.append(".");         
          className.append(LT(n+2).getText());
          n+=2;
        }   
        kjt = getTypeByClassName(className.toString());
        if (kjt != null) { 
           if (LA(n+1) == DOT && LA(n+3) == LPAREN) {
               IteratorOfProgramMethod it = javaInfo.getAllProgramMethods(kjt).iterator();
               while(it.hasNext()) {
                 final ProgramMethod pm = it.next();
                 final String name = kjt.getFullName()+"::"+LT(n+2).getText();
                 if(pm != null && pm.isStatic() && pm.name().toString().equals(name) ) {
                   result = true;
		   break;
		 }
               }
           }   
        }
    } catch (antlr.TokenStreamException tse) {
        // System.out.println("an exception occured"+tse);
        result = false;
    }
    if(result && inputState.guessing > 0) {
      savedGuessing = inputState.guessing;
      inputState.guessing = 0;
    }
    return result;
    }

    private boolean emptyBraces(int lookahead) {
        try {        
            return LA(lookahead) == LBRACE && LA(lookahead+1) == RBRACE;
        } catch (antlr.TokenStreamException tse) {
            return false;
        }
    }

    private TacletBuilder createTacletBuilderFor
        (Object find, int stateRestriction) 
        throws InvalidFindException {
        if ( stateRestriction != RewriteTaclet.NONE && !( find instanceof Term ) ) {        
            String mod;
            switch (stateRestriction) {
                case RewriteTaclet.SAME_UPDATE_LEVEL: 
                       mod = "\"\\sameUpdateLevel\""; 
                break;
                case RewriteTaclet.IN_SEQUENT_STATE: 
                       mod = "\"\\inSequentState\""; 
                break;                
                default: 
                       mod = "State restrictions"; 
                break;                
            }
            
            throw new InvalidFindException
                ( mod +  " may only be used for rewrite taclets:" + find,
                 getFilename(), getLine(), getColumn());
        }
        if ( find == null ) {
            return new NoFindTacletBuilder();
        } else if ( find instanceof Term ) {
            return new RewriteTacletBuilder().setFind((Term)find)
                .setStateRestriction(stateRestriction);
        } else if ( find instanceof Sequent ) {
            Sequent findSeq = (Sequent) find;
            if ( findSeq == Sequent.EMPTY_SEQUENT ) {
                return new NoFindTacletBuilder();
            } else if (   findSeq.antecedent().size() == 1
                          && findSeq.succedent().size() == 0 ) {
                Term findFma = findSeq.antecedent().get(0).formula();
                return new AntecTacletBuilder().setFind(findFma);
            } else if (   findSeq.antecedent().size() == 0
                          && findSeq.succedent().size() == 1 ) {
                Term findFma = findSeq.succedent().get(0).formula();
                return new SuccTacletBuilder().setFind(findFma);
            } else {
                throw new InvalidFindException
                    ("Unknown find-sequent (perhaps null?):"+findSeq,
                     getFilename(), getLine(), getColumn());
            }
        } else {
            throw new InvalidFindException
                    ("Unknown find class type: " + find.getClass().getName(),
                     getFilename(), getLine(), getColumn());
        }
    }       

    private void addGoalTemplate(TacletBuilder b,
                                 String id,
                                 Object rwObj,
                                 Sequent addSeq,
                                 ListOfTaclet addRList,
                                 SetOfSchemaVariable pvs,
                                 SetOfChoice soc) 
        throws SemanticException
        {
            TacletGoalTemplate gt = null;
            if ( rwObj == null ) {
                // there is no replacewith, so we take
                gt = new TacletGoalTemplate(addSeq,
                                            addRList,
                                            pvs);
            } else {
                if ( b instanceof NoFindTacletBuilder ) {
                    // there is a replacewith without a find.
                    throw 
                        new UnfittingReplacewithException
                        ("Replacewith without find", getFilename(),
                         getLine(), getColumn());
                } else if ( b instanceof SuccTacletBuilder
                            || b instanceof AntecTacletBuilder ) {
                    if ( rwObj instanceof Sequent ) {
                        gt = new AntecSuccTacletGoalTemplate(addSeq,
                                                             addRList,
                                                             (Sequent)rwObj,
                                                             pvs);  
                    } else {
                        throw new UnfittingReplacewithException
                            ("Replacewith in a Antec-or SuccTaclet has "+
                             "to contain a sequent (not a term)", 
                             getFilename(), getLine(), getColumn());
                    }
                } else if ( b instanceof RewriteTacletBuilder ) {
                    if ( rwObj instanceof Term ) {
                        gt = new RewriteTacletGoalTemplate(addSeq,
                                                           addRList,
                                                           (Term)rwObj,
                                                           pvs);  
                    } else {
                        throw new UnfittingReplacewithException
                            ("Replacewith in a RewriteTaclet has "+
                             "to contain a term (not a sequent)", 
                             getFilename(), getLine(), getColumn());
                    }
                }
            }
            gt.setName(id); 
            b.addTacletGoalTemplate(gt);
            if(soc != null) b.addGoal2ChoicesMapping(gt,soc);
        }
     
    public void testLiteral(String l1, String l2)
    throws KeYSemanticException
    {
     if (!l1.equals(l2)){
        semanticError("Expecting '"+l1+"', found '"+l2+"'.");
	};
    }

    /** parses a problem but without reading the declarations of
     * sorts, functions and predicates. These have to be given
     * explicitly.
     * the rule sets of the current problem file will be added 
     */ 
    public Term parseTacletsAndProblem() 
    throws antlr.RecognitionException, antlr.TokenStreamException{
        resetSkips();
        skipSorts(); skipFuncs(); skipPreds();    
        return problem();
    }

    /**
     * returns the ProgramMethod parsed in the jml_specifications section.
     */
    public ProgramMethod getProgramMethod(){
        return pm;
    }

    public void addSort(Sort s) {
	sorts().add(s);
    }

    private void addSortAdditionals(Sort s) {
        if (s instanceof NonCollectionSort) {
            NonCollectionSort ns = (NonCollectionSort)s;
            final Sort[] addsort = {
                ns.getSetSort(), ns.getSequenceSort(), ns.getBagSort() 
            };

            for (int i = 0; i<addsort.length; i++) {
                addSort(addsort[i]);
                addSortAdditionals(addsort[i]);
            }
        }
        if ( s instanceof SortDefiningSymbols ) {                        
           ((SortDefiningSymbols)s).addDefinedSymbols(defaultChoice.funcNS(), sorts());
        }
    }

    public void addFunction(Function f) {
        functions().add(f);
    }

    private Sort getIntersectionSort(ListOfString composites) 
                                            throws NotDeclException, KeYSemanticException {
        SetOfSort compositeSorts = SetAsListOfSort.EMPTY_SET;
        final IteratorOfString it = composites.iterator(); 
        while ( it.hasNext () ) {
            final String sortName = it.next();
            final Sort sort = lookupSort(sortName);
            if ( sort == null) {
                throw new NotDeclException("Sort", sortName, 
                    getFilename(), getLine(), getColumn(), 
                    "Components of intersection sorts have to be declared before.");
            }
            compositeSorts = compositeSorts.add(sort);
        }
        final Sort s = IntersectionSort.getIntersectionSort(compositeSorts, sorts(), functions());
        if (!(s instanceof IntersectionSort)) {
            semanticError("Failed to create an intersection sort of " + composites + 
                ". Usually intersection is not required in these cases as \n" + 
                "it is equal to one composite. In this case " + s);            
        }        
        return s;
    }
    
    private HashSet lookupOperatorSV(String opName, HashSet operators) 
    throws KeYSemanticException {
	OperatorSV osv = (OperatorSV)variables().lookup(new Name(opName));
        if(osv == null)
           semanticError("Schema variable "+opName+" not defined.");
        operators.addAll(osv.operators());
        return operators;
    } 
    
    private HashSet opSVHelper(String opName, 
                                HashSet operators,
                                boolean modalOp) 
       throws KeYSemanticException {
       if(opName.charAt(0) == '#') {
          return lookupOperatorSV(opName, operators);           
       }else{
       	  switchToNormalMode();
       	  Operator op;
       	  if (modalOp) {
       	    // modalities are not in the functions namespace
       	    op = Op.getModality(opName);
       	  } else {
           op = (Operator) functions().lookup(new Name(opName));
          }
          switchToSchemaMode();
          if(op == null)
            semanticError("Unrecognised operator: "+opName);
          operators.add(op);
       }
       return operators;
    }

    private void setChoiceHelper(SetOfChoice choices, String section){
        if(choices.size() > 1) {
	   Debug.fail("Don't know what to do with multiple"+
		      "option declarations for "+section+".");
	}
        if(choices.size() == 1) {
             namespaces().setFunctions(choices.iterator().next().funcNS());
        }else{
             namespaces().setFunctions(defaultChoice.funcNS());
	}
    }

    private void semanticError(String message) throws KeYSemanticException {
      throw new KeYSemanticException
        (message, getFilename(), getLine(), getColumn());
    }

    class PairOfStringAndJavaBlock {
      String opName;
      JavaBlock javaBlock;
    }

}

// WATCHOUT Don't remove this. Ever!!! 
// Although it's not called, it is necessary for antlr to produce the 
// right parser.
top {Term a;} : a=formula {	 
   Debug.fail("KeYParser: top() should not be called. Ever.");	 
}	 
;

decls : 
        (one_include_statement)* {
           if(parse_includes) return;
           activatedChoices = SetAsListOfChoice.EMPTY_SET;  
	}
        (options_choice)? { if(onlyWith) return; }
        (
            option_decls
        |    
            sort_decls
        |
            prog_var_decls
        |
            schema_var_decls
        |
            pred_decls
        |
            func_decls
        |
            ruleset_decls

        ) *
    ;

one_include_statement
{
   boolean ldts = false;
}
:
    (INCLUDE | (INCLUDELDTS {ldts = true; }))
    one_include[ldts] (COMMA one_include[ldts])* SEMI
;

one_include [boolean ldt]
{
     String relfile = null;
}
:
        (absfile:IDENT{ 
                if(parse_includes){
                    addInclude(absfile.getText(),false,ldt);
                }
            }
        | relfile = string_literal { 
                if(parse_includes){
                    addInclude(relfile, true,ldt);
                }
            })
    ;

options_choice
:
  (WITHOPTIONS activated_choice (COMMA activated_choice)* SEMI)
;

activated_choice{
    String name;
    Choice c;
}:
        cat:IDENT COLON choice:IDENT
        {if(usedChoiceCategories.contains(cat.getText())){
            throw new IllegalArgumentException("You have already chosen a different option for "+cat.getText());
        }
        usedChoiceCategories.add(cat.getText());
        name = cat.getText()+":"+choice.getText();
        c = (Choice) choices().lookup(new Name(name));
        if(c==null){
            throw new NotDeclException("Option", choice,
                                       getFilename());
        }else{
            activatedChoices=activatedChoices.add(c);
        }
        }
    ;

option_decls
:
        OPTIONSDECL LBRACE (choice SEMI)* RBRACE 
    ;

choice{
    String cat=null;
}:
        category:IDENT {cat=category.getText();} (COLON LBRACE choice_option[cat] (COMMA choice_option[cat])* RBRACE)? 
        {
            if(!category2Default.containsKey(cat)){
                choices().add(new Choice("On",cat));
                choices().add(new Choice("Off",cat)); 
                category2Default.put(cat, cat+":On");               
            }
        }
    ;

choice_option[String cat]{
    String name;
}:
        choice:IDENT { name=cat+":"+choice.getText();
        Choice c = (Choice) choices().lookup(new Name(name));
        if(c==null){
            c = new Choice(choice.getText(),cat);
            choices().add(c);
        }
            if(!category2Default.containsKey(cat)){
                category2Default.put(cat, name);
            }
        }
    ;

sort_decls 
{
  ListOfSort lsorts = SLListOfSort.EMPTY_LIST;
  ListOfSort multipleSorts = SLListOfSort.EMPTY_LIST;
}
: SORTS LBRACE 
       ( multipleSorts = one_sort_decl { lsorts = lsorts.prepend(multipleSorts); })* 
  RBRACE 
     {
        final IteratorOfSort it = lsorts.iterator();
        while (it.hasNext()) {                   
             addSortAdditionals ( it.next() ); 
         }
      }

;

one_sort_decl returns [ListOfSort createdSorts = SLListOfSort.EMPTY_LIST] 
{
    boolean isObjectSort  = false;
    boolean isGenericSort = false;
    boolean isSubSort = false;
    boolean isIntersectionSort = false;
    Sort[] sortExt=new Sort [0];
    Sort[] sortOneOf=new Sort [0];
    String firstSort;
    ListOfString sortIds = SLListOfString.EMPTY_LIST; 
} : 
        ( 
          OBJECT  {isObjectSort =true;} sortIds = objectSortIdentifiers
        | GENERIC {isGenericSort=true;} sortIds = simple_ident_comma_list
            ( ONEOF sortOneOf = oneof_sorts )? 
            ( EXTENDS sortExt = extends_sorts )?
        | sortIds = intersectionSortIdentifier { isIntersectionSort = true; }
        | firstSort = simple_ident_dots { sortIds = sortIds.prepend(firstSort); }
          (
              (EXTENDS sortExt = extends_sorts {  isSubSort = true ; } ) 
            | ((COMMA) sortIds = simple_ident_comma_list { sortIds = sortIds.prepend(firstSort) ; } )
          )?
        ) SEMI {   
            if (!skip_sorts) {
                if (isIntersectionSort) {                    
                    final Sort sort = getIntersectionSort(sortIds);
                    createdSorts = createdSorts.append(sort);
                    addSort(sort); 
                } else {
                    IteratorOfString it = sortIds.iterator ();        
                    while ( it.hasNext () ) {
                        Name sort_name = new Name(it.next());   
                        // attention: no expand to java.lang here!       
                        if (sorts().lookup(sort_name) == null) {
                            Sort s;
                            if (isObjectSort) {
                                if (sort_name.toString().equals("java.lang.Object")) {
                                    if (sorts().lookup(new Name("java.lang.Object")) == null) {
                                        s = new ClassInstanceSortImpl(sort_name, false);
                                    }
                                    s=(Sort)sorts().lookup(new Name("java.lang.Object"));
                                } else {
                                    s = new ClassInstanceSortImpl(sort_name,
                                        (Sort)sorts().lookup(new Name("java.lang.Object")), false);
                                }	
                            } else if (isGenericSort) {
                                int i;
                                SetOfSort  ext   = SetAsListOfSort.EMPTY_SET;
                                SetOfSort  oneOf = SetAsListOfSort.EMPTY_SET;

                                for ( i = 0; i != sortExt.length; ++i )
                                ext = ext.add ( sortExt[i] );

                                for ( i = 0; i != sortOneOf.length; ++i )
                                oneOf = oneOf.add ( sortOneOf[i] );
                                
                                try {
                                    s = new GenericSort(sort_name, ext, oneOf);
                                } catch (GenericSupersortException e) {
                                    throw new GenericSortException ( "sort", "Illegal sort given",
                                        e.getIllegalSort(), getFilename(), getLine(), getColumn());
                                }
                            } else if (new Name("any").equals(sort_name)) {
                                s = Sort.ANY;
                            } else if (isSubSort) {
                                SetOfSort  ext = SetAsListOfSort.EMPTY_SET;

                                for ( int i = 0; i != sortExt.length; ++i )
                                ext = ext.add ( sortExt[i] );

                                s = new PrimitiveSort(sort_name, ext);
                            } else {
                                s = new PrimitiveSort(sort_name);
                            }
                            addSort ( s ); 

                            createdSorts = createdSorts.append(s);
                        }
                    }
                }
            }
        };

intersectionSortIdentifier returns [ListOfString composites = SLListOfString.EMPTY_LIST] 
{
  ListOfString rightComposites;
  String left = ""; 
  String right = "";   
}
:     
     INTERSECTIONSORT LPAREN 
        (left  = simple_ident_dots) COMMA 
        (rightComposites = intersectionSortIdentifier {            
            final IteratorOfString it = rightComposites.iterator();
            right = "\\inter(" + it.next() + "," + it.next() +")";
        } | right = simple_ident_dots) RPAREN 
     {
         composites = composites.prepend(right).prepend(left);
     }
;

objectSortIdentifiers returns [ListOfString ids = SLListOfString.EMPTY_LIST]
{
  String id;
}
 :
  id = simple_ident_dots { ids = ids.append ( id );} 
  (COMMA id = simple_ident_dots { ids = ids.append ( id );})*
 ;


simple_ident_dots returns [ String ident = ""; ] 
{
  String id = null;
}
:
  id = simple_ident { ident += id; }  
    (DOT 
 	(id = simple_ident | num:NUM_LITERAL {id=num.getText();}) 
 	{ident += "." + id;})* 
 ;

extends_sorts returns [Sort[] extendsSorts = null] 
{
    List args = new LinkedList();
    Sort s;
}
    :
        s = any_sortId_check[!skip_sorts] { args.add(s); }
        (
            COMMA s = any_sortId_check[!skip_sorts] {args.add(s);}
        ) *
        {
            extendsSorts = (Sort[])args.toArray(AN_ARRAY_OF_SORTS);
        }
    ;

oneof_sorts returns [Sort[] oneOfSorts = null] 
{
    List args = new LinkedList();
    Sort s;
}
    : LBRACE
        s = sortId_check[true] { args.add(s); }
        (
            COMMA s = sortId_check[true] {args.add(s);}
        ) *
      RBRACE {
        oneOfSorts = (Sort[])args.toArray(AN_ARRAY_OF_SORTS);
      }
    ;

keyjavatype returns [KeYJavaType kjt=null]
{ 
   String type = null;
   boolean array = false;

}
:
   type = simple_ident_dots (EMPTYBRACKETS {type += "[]"; array=true;})* {

     kjt = getJavaInfo().getKeYJavaType(type);
            
     if (kjt == null) {
       //expand to "java.lang"
       String guess = "java.lang."+type;
       kjt = getJavaInfo().getKeYJavaType(guess);       
       if (array) {
          try {
            JavaBlock jb = getJavaInfo().readJavaBlock("{" + type + " k;}");
            kjt = ((VariableDeclaration) 
                    ((StatementBlock) jb.program()).getChildAt(0)).
                        getTypeReference().getKeYJavaType();
//            kjt = getJavaInfo().getKeYJavaType(type);
          } catch (Exception e) {
             kjt = null;
          }          
       }
     }
	
     if (kjt == null) {
       semanticError("Unknown type: " + type);
     }
   }
 ;

prog_var_decls 
{
    String var_name;
    KeYJavaType kjt = null;
    ListOfString var_names = null;
}
    :
        { switchToNormalMode();}
        PROGRAMVARIABLES
        LBRACE 
        (
            kjt = keyjavatype
            var_names = simple_ident_comma_list
            {
	        IteratorOfString it = var_names.iterator();
		while(it.hasNext()){
		  var_name = it.next();
		  ProgramElementName pvName = new ProgramElementName(var_name);
		  Named name = lookup(pvName);
                  if (name != null ) {
		    // commented out as pv do not have unique name (at the moment)
		    //  throw new AmbigiousDeclException
     		    //  	(var_name, getFilename(), getLine(), getColumn()); 
		    if(name instanceof ProgramVariable && 
			    !((ProgramVariable)name).getKeYJavaType().equals(kjt)) { 
                      namespaces().programVariables().add(new LocationVariable
                        (pvName, kjt));
		    }
                  }else{
                     namespaces().programVariables().add(new LocationVariable
                        (pvName, kjt));
		  }
	       }
            }
            SEMI
        ) *
        RBRACE
    ;

string_literal returns [String lit = null]
   :
     id:STRING_LITERAL {
       lit = id.getText();
       lit = lit.substring(1,lit.length()-1);
       stringLiteralLine = id.getLine();
     }
     ;

simple_ident returns [String ident = null]
   :
     id:IDENT { ident = id.getText(); }
   ;

simple_ident_comma_list returns [ListOfString ids = SLListOfString.EMPTY_LIST]
{
  String id = null;
}
   :
   id = simple_ident { ids = ids.append(id); }
   (COMMA id = simple_ident { ids = ids.append(id); })*
 ;


schema_var_decls :
        SCHEMAVARIABLES LBRACE  { switchToSchemaMode(); }
  	  ( one_schema_var_decl )*
        RBRACE { switchToNormalMode(); }
    ;
 
one_schema_var_decl 
{
    Sort s = null;
    boolean makeVariableSV  = false;
    boolean makeSkolemTermSV = false;
    boolean makeLocationsSV	= false;
    boolean makeFunctionsSV  = false;
    boolean modalOpSV       = false;
    String id = null;
    ListOfString ids = null;
    SchemaVariableModifierSet mods = null;
} :   
   ((MODALOPERATOR {modalOpSV = true;} | OPERATOR {modalOpSV = false;} ) 
       one_schema_op_decl[modalOpSV] SEMI)
 |
  ( 
   (
    PROGRAM
    { mods = new SchemaVariableModifierSet.ProgramSV (); }
    ( schema_modifiers[mods] ) ?
    id = simple_ident  {
       s = (Sort)ProgramSVSort.name2sort().get(new Name(id));
       if (s == null) {
         semanticError
           ("Program SchemaVariable of type "+id+" not found.");
       }
    }
    ids = simple_ident_comma_list
  | FORMULA
    { mods = new SchemaVariableModifierSet.FormulaSV (); }
    ( schema_modifiers[mods] ) ?
    {s = Sort.FORMULA;}
    ids = simple_ident_comma_list 
  | LOCATION
    { makeLocationsSV = true; 
      mods = new SchemaVariableModifierSet.ListSV(); }
    ( schema_modifiers[mods] ) ?    
    ids = simple_ident_comma_list 
  | FUNCTION
    { makeFunctionsSV = true; 
      mods = new SchemaVariableModifierSet.ListSV(); }
    ( schema_modifiers[mods] ) ?
    ids = simple_ident_comma_list 
  | (    TERM
         { mods = new SchemaVariableModifierSet.TermSV (); }
         ( schema_modifiers[mods] ) ?
      | (VARIABLES
         {makeVariableSV = true;}
         { mods = new SchemaVariableModifierSet.VariableSV (); }
         ( schema_modifiers[mods] ) ?)
      | (SKOLEMTERM {makeSkolemTermSV = true;}
         { mods = new SchemaVariableModifierSet.SkolemTermSV (); }
         ( schema_modifiers[mods] ) ?)
    )
    s = any_sortId_check[true]
    ids = simple_ident_comma_list 
  ) SEMI
   { 
     IteratorOfString it = ids.iterator();
     while(it.hasNext())
       schema_var_decl(it.next(),s,makeVariableSV,makeSkolemTermSV, 
       				   makeLocationsSV, makeFunctionsSV, mods);
   }
 )

 ;

schema_modifiers[SchemaVariableModifierSet mods]
{
    ListOfString opts = null;
}
    :
        LBRACKET
        opts = simple_ident_comma_list         
        RBRACKET
        {
            final IteratorOfString it = opts.iterator ();
            while ( it.hasNext () ) {
                final String option = it.next();
                if (!mods.addModifier(option))
                    semanticError(option+ 
                    ": Illegal or unknown modifier in declaration of schema variable");
            }
        }
    ;

one_schema_op_decl[boolean modalOp]
{
    HashSet operators = new HashSet(50);
    String id = null;
    Sort sort = Sort.FORMULA;
    ListOfString ids = null;
} 
    :
        (LPAREN sort = any_sortId_check[true] {
           if (modalOp && sort != Sort.FORMULA) { 
               semanticError("Modal operator SV must be a FORMULA, not " + sort);
           }            
         } RPAREN)? 
        LBRACE ids = simple_ident_comma_list RBRACE id = simple_ident
	{   if (skip_schemavariables) {	       
	       return;
	    }	        
            IteratorOfString it1 = ids.iterator();
            while(it1.hasNext()) {
  	      operators = opSVHelper(it1.next(), operators, modalOp);
  	    }
            SchemaVariable osv = (SchemaVariable)variables().lookup(new Name(id));
            if(osv != null)
              semanticError("Schema variable "+id+" already defined.");
	    Iterator it2 = operators.iterator();
	    int arity = ((Operator)it2.next()).arity();
	    while(it2.hasNext())
              if(arity != ((Operator)it2.next()).arity())
                semanticError("Arity mismatch for schema variable "+id);

            osv = SchemaVariableFactory.createOperatorSV(new Name(id), 
                        modalOp ? Modality.class : Operator.class, 
                        sort, arity, operators);
            
            if (inSchemaMode()) {
                variables().add(osv);
                functions().add(osv);
            }
        }
    ;

pred_decl
{
    Sort[] argSorts;    
    String pred_name;
    List dependencyListList = null;
    boolean nonRigid = false;
    int location = NORMAL_NONRIGID;
}
    :
        (NONRIGID {nonRigid=true;}(LBRACKET location = location_ident RBRACKET)?)?
        pred_name = funcpred_name
        (
            LBRACKET
            dependencyListList = dependency_list_list
            RBRACKET
            {
                if (!nonRigid) {
                    semanticError(pred_name+
		      ": Predicate declarations with attribute lists must use the '\\nonRigid' modifier");
                }
                pred_name = KeYParser.createDependencyName(pred_name,
                                                           dependencyListList);
            }
        )?
        argSorts = arg_sorts[!skip_predicates]
        {
            if (!skip_predicates) {
                Name predicate = new Name(pred_name);		    		                        
                Function p = null;
                if (lookup(predicate) != null) {
                    throw new AmbigiousDeclException
                    (pred_name, getFilename(), getLine(), getColumn());
                } else if (nonRigid) {
                    if (dependencyListList != null) {
                        p = NRFunctionWithExplicitDependencies.getSymbol
                            (predicate, Sort.FORMULA, 
                             new ArrayOfSort(argSorts),
                             extractPartitionedLocations(dependencyListList));
                    } else {
	        	switch (location) {
                           case NORMAL_NONRIGID:                         
                              p = new NonRigidFunction(predicate, Sort.FORMULA, argSorts);                           
                              break;
                           case LOCATION_MODIFIER: 
                              semanticError("Modifier 'Location' not allowed for non-rigid predicates.");
                              break;
                 	  case HEAP_DEPENDENT: p = new NonRigidHeapDependentFunction(predicate, Sort.FORMULA, argSorts);      
                 	      break;
                 	  default:
                 	     semanticError("Unknown modifier used in declaration of non-rigid predicate "+predicate);
                 	}
                    }

                } else {
                   p = new RigidFunction(predicate, Sort.FORMULA, argSorts);
                }
                assert p != null;
                addFunction(p);         
            } 
        }
        SEMI
    ;

pred_decls 
{
    SetOfChoice choices = SetAsListOfChoice.EMPTY_SET;
}
    :
        PREDICATES (choices=option_list[choices])? 
	{
           setChoiceHelper(choices,"predicates");
	}
        LBRACE
        (
            pred_decl
        ) *
        RBRACE
    {
           setChoiceHelper(SetAsListOfChoice.EMPTY_SET, "predicates");
    }
    ;


location_ident returns [int kind = NORMAL_NONRIGID]
{ String id = null; }
    :
        id = simple_ident
       { 
          if ("Location".equals(id)) {
             kind = LOCATION_MODIFIER;
          } else if ("HeapDependent".equals(id)) {
             kind = HEAP_DEPENDENT;
          } else if (!"Location".equals(id)) {
            semanticError(
                id+": Attribute of a Non Rigid Function can only be 'Location'");        
          }
       }
    ;



func_decl
{
    Sort[] argSorts;
    Sort retSort;
    String func_name;
    List dependencyListList = null;
    boolean nonRigid = false;
    String id = null;
    int location = NORMAL_NONRIGID;
}
    :
        (NONRIGID {nonRigid=true;} (LBRACKET location = location_ident RBRACKET)?)?
        retSort = sortId_check[!skip_functions]
        func_name = funcpred_name 
        (
            LBRACKET
            dependencyListList = dependency_list_list
            RBRACKET
            {
                if (!nonRigid)
                {
                    semanticError(func_name+
		      ": Function declarations with attribute lists	must use the '\\nonRigid' modifier");
                }
                func_name = KeYParser.createDependencyName(func_name,
                                                           dependencyListList);
            }
        )?
        argSorts = arg_sorts[!skip_functions]
        {
            if (!skip_functions) {
                Name fct_name = new Name(func_name);
                Function f = null;
                if (lookup(fct_name) != null) {
                    throw new AmbigiousDeclException
                    (func_name, getFilename(), getLine(), getColumn());
                } else if (nonRigid) {
                    if (dependencyListList != null) {
                        f = NRFunctionWithExplicitDependencies.getSymbol
                            (fct_name, retSort, 
                             new ArrayOfSort(argSorts),
                             extractPartitionedLocations(dependencyListList));
                    } else {
                        switch (location) {
                           case NORMAL_NONRIGID: f = new NonRigidFunction(fct_name, retSort, argSorts);
                              break;
                           case LOCATION_MODIFIER: f = new NonRigidFunctionLocation(fct_name, retSort, argSorts);
                              break;
                 	  case HEAP_DEPENDENT: f = new NonRigidHeapDependentFunction(fct_name, retSort, argSorts);      
                 	      break;
                 	  default:
                 	     semanticError("Unknwon modifier used in declaration of non-rigid function "+fct_name);
                 	}
                    }
                } else {
                    f = new RigidFunction(fct_name, retSort, argSorts);
                }
                assert f != null;
                addFunction(f);
            } 
        }
        SEMI
    ;

func_decls 
{
    SetOfChoice choices = SetAsListOfChoice.EMPTY_SET;
}
    :
        FUNCTIONS (choices=option_list[choices])? 
	{
           setChoiceHelper(choices,"functions");
	}
        LBRACE 
        (
            func_decl
        ) *
        RBRACE
    {
           setChoiceHelper(SetAsListOfChoice.EMPTY_SET, "functions");
    }
    ;

dependency_list_list returns [List dependencyListList = new LinkedList()]
{
    List dependencyList;
}
    :
        dependencyList = dependency_list {dependencyListList.add(dependencyList);}
        (OR dependencyList = dependency_list {dependencyListList.add(dependencyList);})*
    ;

dependency_list returns [List dependencyList = new LinkedList()]
{
    String attribute;
    KeYJavaType componentType;
}
    :
        (
            (
                (attribute = attrid) {dependencyList.add(attribute);}
            |
                (componentType = arrayopid) {dependencyList.add(componentType);}
            )
            SEMI
        )+
    ;

arrayopid returns [KeYJavaType componentType = null]
    :
        EMPTYBRACKETS
        LPAREN
        componentType = keyjavatype
        RPAREN
    ;

arg_sorts[boolean checkSort] returns [Sort[] argSorts = null] 
{
    List args = new LinkedList();
    Sort s;
}
    :
        (
            LPAREN
            s = sortId_check[checkSort] { args.add(s); }
            (
                COMMA s = sortId_check[checkSort] {args.add(s);}
            ) *
            RPAREN
        ) ?
        {
            argSorts = (Sort[])args.toArray(AN_ARRAY_OF_SORTS);
        }
    ;

ruleset_decls
{
  String id = null;
}
    :
        HEURISTICSDECL
        LBRACE
        (
            id = simple_ident SEMI
            { 
                if (!skip_rulesets) {
                    RuleSet h = new RuleSet(new Name(id));
                    if(ruleSets().lookup(new Name(id))==null){
                        ruleSets().add(h);
                    }
                }
            }
        ) *
        RBRACE
    ;

sortId  returns [Sort s = null]
    :
        s = sortId_check[true]
    ;           

// Non-generic sorts, array sorts allowed
sortId_check [boolean checkSort] returns [Sort s = null]                
{
    Sort t;
}
    :
        t = sortId_check_help[checkSort]
        s = array_set_decls[t]
    ;

// Generic and non-generic sorts, array sorts allowed
any_sortId_check [boolean checkSort] returns [Sort s = null]                
{
    Sort t;
}
    :   
        t = any_sortId_check_help[checkSort]
        s = array_set_decls[t]
    ;

// also allow generic sorts
any_sortId_check_help [boolean checkSort] returns [Sort s = null]
{
    String name;
}
    :
        name = simple_sort_name 
        {  s = lookupSort(name);
           if (checkSort && s == null) {
                throw new NotDeclException("sort", name, 
                                           getFilename(), 
                                           getLine(), getColumn());
           }
        }
    ;

sortId_check_help [boolean checkSort] returns [Sort s = null]
    :
        s = any_sortId_check_help[checkSort]
        {
            // don't allow generic sorts or collection sorts of
            // generic sorts at this point
            Sort t = s;
            while ( t != Sort.NULL && t instanceof CollectionSort ) {
            	t = ((CollectionSort)t).elementSort ();
            }

            if ( t instanceof GenericSort ) {
                throw new GenericSortException ( "sort",
                    "Non-generic sort expected", t,
                    getFilename (), getLine (), getColumn () );
            }
        }
    ;

empty_set_braces returns [String result = null]
:
   LBRACE RBRACE { result = "{}".intern(); }
;

array_set_decls[Sort p] returns [Sort s = null]                
{
    String sortName = "";
    String emptybraces = null;
    int  n = 0;    
}

    :
     (EMPTYBRACKETS {n++;})*
        { 
            if (n != 0){
                final JavaInfo ji = getJavaInfo();
                s = ArraySortImpl.getArraySortForDim(
                    p, n, ji.getJavaLangObjectAsSort(),
                    ji.getJavaLangCloneableAsSort(), 
                    ji.getJavaIoSerializableAsSort());
            } else {
                s = p;
            }
        }     
        ({ if (s != null) { 
                    sortName = s.name() + "";
                }
            }  
             (emptybraces = empty_set_braces {                  
                    
                    sortName += emptybraces; 
                    s = lookupSort(sortName);
                    if (s == null) {
                        throw new NotDeclException("sort", sortName, 
                            getFilename(), 
                            getLine(), getColumn());
                    }
                })*)
      
            
    ;

attrid returns [String attr = "";]
{
  String id = null;
  String classRef = "";
  KeYJavaType kjt = null;
  boolean brackets = false;
} : 
        
    id = simple_ident 
       (AT LPAREN classRef = simple_ident_dots (EMPTYBRACKETS {brackets = true;})? RPAREN {
            if(brackets) classRef += "[]";
            if (!isDeclParser()) {
	        kjt = getTypeByClassName(classRef);
		if(kjt == null)
                  throw new NotDeclException
                    ("Class " + classRef + " is unknown.", 
                     classRef, getFilename(), getLine(), 
                     getColumn());
		classRef = kjt.getFullName();
            }
         classRef+="::";
       })? 
    {
	attr = classRef+id;
    }
    ;

id_declaration returns [ IdDeclaration idd = null ]
{
    Sort s = null;
}
    :
        id:IDENT
        ( COLON s = sortId_check[true] ) ?
        {
            idd = new IdDeclaration ( id.getText (), s );
        }
    ;

funcpred_name returns [String result = null]
{
  String name = null;
  String prefix = null;
}
    :
     
    (sort_name DOUBLECOLON) => (prefix = sort_name 
        DOUBLECOLON name = simple_ident {result = prefix + "::" + name;})
  | 
    (prefix = simple_ident {result = prefix; })
;


// no array and set sorts
simple_sort_name returns [String name = ""]
{ String id = ""; }
    :
        id = simple_ident_dots  { name = id; } 
        | inter:INTERSECTIONSORT {name += inter.getText();} LPAREN 
             id = simple_ident_dots { name += "(" + id;  } COMMA 
             id = simple_sort_name  { name +=  "," + id + ")"; }          
          RPAREN
    ;


sort_name returns [String name = null]
{
  String emptybraces = "";
}
    :
        name = simple_sort_name     
        (emptybraces = empty_set_braces {name += emptybraces;} |
         brackets:EMPTYBRACKETS {name += brackets.getText();} )*
;

/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term' 
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */

formula returns [Term a = null] 
    :
        a = term 
        {
            if (a != null && a.sort() != Sort.FORMULA ) {
                semanticError("Just Parsed a Term where a Formula was expected.");
            }
        }
    ;

term returns [Term a = null] 
    :
        a=term20 
    ;

    
location_list returns [SetOfLocationDescriptor set = SetAsListOfLocationDescriptor.EMPTY_SET;]
{
	LocationDescriptor loc;
}
:
	LBRACE
	(
      	loc=location_descriptor {set = set.add(loc);}
      	(
      		COMMA loc=location_descriptor {set = set.add(loc);}
      	)*
    )?
    RBRACE
;


location_descriptor returns [LocationDescriptor loc = null]
{
	ListOfQuantifiableVariable boundVars = null;
	Term f = tf.createJunctorTerm(Op.TRUE);
	Term t;
}
:
   {
		quantifiedArrayGuard = tf.createJunctorTerm(Op.TRUE);
   }
   (
	STAR {loc = EverythingLocationDescriptor.INSTANCE;}
    | (
	(FOR boundVars=bound_variables)?
    	((IF) => IF LPAREN f=formula RPAREN)?
       	t=accessterm {
          if(boundVars != null) {	  
             while(!boundVars.isEmpty()) {
    	        unbindVars();
        	    boundVars = boundVars.tail();
             }
	  }	  
     	  quantifiedArrayGuard = tf.createJunctorTermAndSimplify(Op.AND, f, quantifiedArrayGuard);       
	  loc = new BasicLocationDescriptor(quantifiedArrayGuard, t);
	}
      )
   )
   {
		quantifiedArrayGuard = null;
   }
;


term20 returns [Term a = null] 
{
    Term a1;
}
    :   a=term30 
        (EQV a1=term30 
            { a = tf.createJunctorTerm(Op.EQV, new Term[]{a, a1});} )*
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

term30 returns [Term a = null] 
{
    Term a1;
}
    :   a=term40 
        (IMP a1=term30 
            { a = tf.createJunctorTerm(Op.IMP, new Term[]{a, a1});} )?
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

term40 returns [Term a = null] 
{
    Term a1;
}
    :   a=term50 
        (OR a1=term50 
            { a = tf.createJunctorTerm(Op.OR, new Term[]{a, a1});} )*
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

term50 returns [Term a = null] 
{
    Term a1;
}
    :   a=term60 
        (AND a1=term60
            { a = tf.createJunctorTerm(Op.AND, new Term[]{a, a1});} )*
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

term60 returns [Term a = null] 
    :  
        a = unary_formula
    |   a = term70
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

unary_formula returns [Term a = null] 
{ Term a1; }
    :  
        NOT a1  = term60 { a = tf.createJunctorTerm(Op.NOT,new Term[]{a1}); }
    |	a = quantifierterm 
    |   a = modality_dl_term
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

term70 returns [Term a = null] 
{
    Term a1;
    boolean negated = false;
}
    :
        a =  logicTermReEntry // accessterm 
        // a term like {o:=u}x=y is parsed as {o:=u}(x=y)
        (  
	    (EQUALS | NOT_EQUALS {negated = true;}) a1 = logicTermReEntry
            { 
                if (a.sort() == Sort.FORMULA ||
                    a1.sort() == Sort.FORMULA) {
                    String errorMessage = 
                    "The term equality \'=\'/\'!=\' is not "+
                    "allowed between formulas.\n Please use \'" + Op.EQV +
                    "\' in combination with \'" + Op.NOT + "\' instead.";
                if (a.op() == Op.TRUE || a.op() == Op.FALSE ||
                    a1.op() == Op.TRUE || a1.op() == Op.FALSE) {
                    errorMessage += 
                    " It seems as if you have mixed up the boolean " +
                    "constants \'TRUE\'/\'FALSE\' " +
                    "with the formulas \'true\'/\'false\'.";
                }
                semanticError(errorMessage);
            }
            a = tf.createEqualityTerm(a, a1);

            if (negated) {
              a = tf.createJunctorTerm(Op.NOT, a);
            }
        })?
 ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

relation_op returns [Function op = null]
{
  String op_name = null;
}
:
 (
    LESS         { op_name = "lt"; }
 |  LESSEQUAL    { op_name = "leq"; }
 |  GREATER      { op_name = "gt"; }
 |  GREATEREQUAL { op_name = "geq"; }
 ) {
     op = (Function) functions().lookup(new Name(op_name)); 
     if(op == null) {
       semanticError("Function symbol '"+op_name+"' not found.");
     }
   }
;

weak_arith_op returns [Function op = null]
{
  String op_name = null;
}
:
 (
    PLUS         { op_name = "add"; }
 |  MINUS        { op_name = "sub"; }
 ) {
     op = (Function) functions().lookup(new Name(op_name)); 
     if(op == null) {
       semanticError("Function symbol '"+op_name+"' not found.");
     }
   }
 
;

strong_arith_op returns [Function op = null]
{
  String op_name = null;
}
:
 (
    STAR         { op_name = "mul"; }
 |  SLASH        { op_name = "div"; }
 |  PERCENT      { op_name = "mod"; }
 ) {
     op = (Function) functions().lookup(new Name(op_name)); 
     if(op == null) {
       semanticError("Function symbol '"+op_name+"' not found.");
     }
   }
;

// term80
logicTermReEntry returns [Term a = null]
{
  Term a1 = null;
  Function op = null;
}
:
   a = term90 ((relation_op)=> op = relation_op a1=term90 {
                 a = tf.createFunctionTerm(op, a, a1);
              })?
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }


term90 returns [Term a = null]
{
  Term a1 = null;
  Function op = null;
}
:
   a = term100 ( op = weak_arith_op a1=term100 {
                  a = tf.createFunctionTerm(op, a, a1);
                })*
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

term100 returns [Term a = null]
{
  Term a1 = null;
  Function op = null;
}
:
   a = term110 ( op = strong_arith_op a1=term110 {
                  a = tf.createFunctionTerm(op, a, a1);
                })*
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }


/**
 * helps to better distinguish if formulas are allowed or only term are
 * accepted
 * WATCHOUT: Woj: the check for Sort.FORMULA had to be removed to allow
 * infix operators and the whole bunch of grammar rules above.
 */
term110 returns [Term result = null]
    :
        (
            result = accessterm |
            result = update_or_substitution
        ) 
        {
	/*
            if (result.sort() == Sort.FORMULA) {
                semanticError("Only terms may stand here.");
            }
	*/
        }          
    ;
 
// WATCHOUT: Woj: not used anymore, but don't remove,
// very useful piece of code
/*
classReference returns [String classReference = ""]
{}:
        
        id:IDENT {
            classReference = id.getText(); 
            while (isPackage(classReference)) {
                match(DOT);
                classReference += "." + LT(1).getText();
                match(IDENT);
            }      
            KeYJavaType kjt = null;
	    kjt = getTypeByClassName(classReference);
            if ( kjt == null) {
                throw new NotDeclException
                    ("Class " + classReference + " is unknown.", 
                     classReference, getFilename(), getLine(), 
                     getColumn());
            }
	    classReference = kjt.getFullName();
        }  
    ;
*/


transactionNumber returns [Term trans = null]
:
     EXP LPAREN trans = term60 RPAREN
     |
     p:PRIMES {
       int primes = p.getText().length();
       if(parsingContracts) {
         if(primes != 1) {
           semanticError("In contracts only one prime is allowed "+
	     "(equivalent to ^(de.uka.ilkd.key.javacard.KeYJCSystem.<transactionCounter>)).");
	 }
         // Woj's solution
         //TermSymbol v = getAttribute(
         //  getTypeByClassName("de.uka.ilkd.key.javacard.KeYJCSystem").getSort(),
         //  "de.uka.ilkd.key.javacard.KeYJCSystem::<transactionCounter>"); 
	 //trans = createAttributeTerm(null, v, null);
	 // Richard's solution
	 final ProgramVariable op = getServices().getJavaInfo().getAttribute
           (JVMIsTransientMethodBuilder.IMPLICIT_TRANSACTION_COUNTER, 
            "de.uka.ilkd.key.javacard.KeYJCSystem");
         if(op == null) {
           semanticError("Attribute " +
            JVMIsTransientMethodBuilder.IMPLICIT_TRANSACTION_COUNTER +
            " of type " + "de.uka.ilkd.key.javacard.KeYJCSystem" + " not known. " + 
            "Did you place appropriate Java Card API to your sources?");
         }
         trans = tf.createVariableTerm(op);
       }else{
         trans = toZNotation(""+primes, functions(), tf);
       }
     }
;


staticAttributeOrQueryReference returns [String attrReference = ""]
:
        
      //  attrReference=simple_ident_dots 
      id:IDENT
        {
            attrReference = id.getText(); 
            while (isPackage(attrReference) || LA(2)==NUM_LITERAL || 
                (LT(2).getText().charAt(0)<='Z' && LT(2).getText().charAt(0)>='A' && 
	    		(LT(2).getText().length()==1 || LT(2).getText().charAt(1)<='z' && LT(2).getText().charAt(1)>='a'))) {
                match(DOT);
                attrReference += "." + LT(1).getText();
                if(LA(1)==NUM_LITERAL){
                	match(NUM_LITERAL);
                }else{
               	 	match(IDENT);
                }
            }      
        }
        (EMPTYBRACKETS {attrReference += "[]";})*    
        {   KeYJavaType kjt = null;
            kjt = getTypeByClassName(attrReference);
            if (kjt == null) {
                throw new NotDeclException
                    ("Class " + attrReference + " is unknown.", 
                     attrReference, getFilename(), getLine(), 
                     getColumn());
            }	        
            attrReference = kjt.getSort().name().toString();            
            match(DOT);
            attrReference += "::" + LT(1).getText();
            match(IDENT);
	    if(savedGuessing > -1) {
	      inputState.guessing = savedGuessing;
	      savedGuessing = -1;
	    }
        }  
    ;

static_attribute_suffix returns [Term result = null]
{
    TermSymbol v = null;
    Term shadowNumber  = null;
    String attributeName = "";
}    
    :   
        attributeName = staticAttributeOrQueryReference
        {   
         	String className;
            if(attributeName.indexOf(':')!=-1){	
	       		className = 
		   			attributeName.substring(0, attributeName.indexOf(':'));
            }else{
          		className = 
		   			attributeName.substring(0, attributeName.lastIndexOf("."));	
            }	
	       	v = getAttribute(getTypeByClassName(className).getSort(), attributeName); 
	    }
        (shadowNumber = transactionNumber)?
        { result = createAttributeTerm(null, v, shadowNumber); }                   
 ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }


attribute_or_query_suffix[Term prefix] returns [Term result = null]
{
    TermSymbol v = null;
    Term shadowNumber = null;
    result = prefix;
    String attributeName = "";    
}    
    :   
        DOT 
        ((IDENT (AT LPAREN simple_ident_dots RPAREN)? LPAREN)=>( result = query[prefix])
         | 
            attributeName = attrid 
            {   
            	v = getAttribute(prefix.sort(), attributeName);             	
            }   
            ( 

                ( shadowNumber = transactionNumber )?
                {
                    result = createAttributeTerm(prefix, v, shadowNumber);
                }        
            ))
 ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

query [Term prefix] returns [Term result = null] 
{
    String classRef = "";
    Term[] args = null;
    PairOfTermArrayAndBoundVarsArray argsWithBoundVars = null; 
    boolean brackets = false;
}
    :
    mid:IDENT (AT LPAREN classRef = simple_ident_dots (EMPTYBRACKETS {brackets = true;} )? RPAREN)? argsWithBoundVars = argument_list
    { 
       if("".equals(classRef)){
          classRef = prefix.sort().name().toString();
       }else{
         if(brackets) classRef += "[]";
         KeYJavaType kjt = getTypeByClassName(classRef);
         if(kjt == null)
           throw new NotDeclException
             ("Class " + classRef + " is unknown.", 
              classRef, getFilename(), getLine(), 
              getColumn());
         classRef = kjt.getFullName();
       }
       if (argsWithBoundVars != null) {
         args = argsWithBoundVars.getTerms();
       }
       result = getServices().getJavaInfo().getProgramMethodTerm
                (prefix, mid.getText(), args, classRef);
    }        
 ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(),getColumn()));

        }

static_query returns [Term result = null] 
{
    String queryRef = "";
    Term[] args = null;
    PairOfTermArrayAndBoundVarsArray argsWithBoundVars = null; 
    TermSymbol ts = null;
}
    :
    queryRef =  staticAttributeOrQueryReference argsWithBoundVars = argument_list
    { 
       if (argsWithBoundVars != null) {
         args = argsWithBoundVars.getTerms();
       }

       int index = queryRef.indexOf(':');
       String className = queryRef.substring(0, index); 
       String qname = queryRef.substring(index+2); 
       result = getServices().getJavaInfo().getProgramMethodTerm(null, qname, args, className);
       if(result == null && isTermParser()) {
	  final Sort sort = lookupSort(className);
          if (sort == null) {
		semanticError("Could not find matching sort for " + className);
          }
          KeYJavaType kjt = getServices().getJavaInfo().getKeYJavaType(sort);
          if (kjt == null) {
		semanticError("Found logic sort for " + className + 
		 " but no corresponding java type (e.g. int is only " +
		 " available as logic sort not as java type use (jint, jbyte, jshort etc. instead)");
          }          
       }
	    
    }        
 ; exception
        catch [TermCreationException ex] {
        keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(),getColumn()));

        }

//term120
accessterm returns [Term result = null] 
{
    Sort s = null;
}
    :
      (MINUS ~NUM_LITERAL) => MINUS result = term110
        {
            if (result.sort() != Sort.FORMULA) {
                result = tf.createFunctionTerm
                ((Function) functions().lookup(new Name("neg")), result);
            } else {
                semanticError("Formula cannot be prefixed with '-'");
            }
        } 
      |
      (LPAREN any_sortId_check[false] RPAREN term110)=> 
        LPAREN s = any_sortId_check[true] RPAREN result=term110 {
         if(s==null) {
           semanticError("Tried to cast to unknown type.");
         } else if ((s instanceof PrimitiveSort) && 
             (result.sort() instanceof ObjectSort)) {
                semanticError("Illegal cast from " + result.sort() + 
                    " to sort " + s +
                    ". Casts between primitive and reference types are not allowed. ");
         }
         result = tf.createFunctionTerm(((AbstractSort)s).getCastSymbol(), result);
	  } |
      ( {isStaticQuery()}? // look for package1.package2.Class.query(
        result = static_query
      | 
        {isStaticAttribute()}?            // look for package1.package2.Class.attr
        result = static_attribute_suffix
      | 	
        result = term130
      )   
         ( result = array_access_suffix[result] | result = attribute_or_query_suffix[result] )*
 ; exception
        catch [TermCreationException ex] {
              semanticError(ex.getMessage());
        }



array_access_suffix [Term arrayReference] returns [Term result = arrayReference] 
{
    Term indexTerm  = null;
    Term shadowNumber = null;
    Term rangeFrom = null;
    Term rangeTo   = null;     
    Sort arraySort = null;
}
	:
  	LBRACKET 
	(   STAR {
           	rangeFrom = toZNotation("0", functions(), tf);
           	Term lt = createAttributeTerm(result, getAttribute(result.sort(), "length"), null);
           	Term one = toZNotation("1", functions(), tf);
  	   		rangeTo = tf.createFunctionTerm
           		((Function) functions().lookup(new Name("sub")), lt, one); 
        } 
        | indexTerm = logicTermReEntry 
	        ((DOTRANGE) => DOTRANGE rangeTo = logicTermReEntry
		                 {rangeFrom = indexTerm;})?
    )
    RBRACKET (AT LPAREN arraySort = any_sortId_check[true] RPAREN)? ( shadowNumber = transactionNumber )? 
    {
       if (arraySort == null) {
       	if ( inSchemaMode() ) {
          if ( parsingFind ) {
		semanticError("Array operators occuring in the focus term must be fully qualified"+
			      " (e.g. a[i]@(int[]).");
          }
          arraySort = result.sort(); 
       	} else {
       	  arraySort = result.sort();	
       	}
       }
       
       
	if(rangeTo != null) {
		if(quantifiedArrayGuard == null) {
			semanticError(
  		  	"Quantified array expressions are only allowed in locations.");
		}
		LogicVariable indexVar = new LogicVariable(new Name("i"), 
		   	   		   (Sort) sorts().lookup(new Name("int")));
		indexTerm = tf.createVariableTerm(indexVar);
		   	
		Function leq = (Function) functions().lookup(new Name("leq"));
		Term fromTerm = tf.createFunctionTerm(leq, rangeFrom, indexTerm);
		Term toTerm = tf.createFunctionTerm(leq, indexTerm, rangeTo);
		Term guardTerm = tf.createJunctorTerm(Op.AND, fromTerm, toTerm);
		quantifiedArrayGuard = tf.createJunctorTermAndSimplify(Op.AND, 
		   						  quantifiedArrayGuard, 
		   						  guardTerm);
		}
        if (shadowNumber != null) {
            result = tf.createShadowArrayTerm
                      (ShadowArrayOp.getShadowArrayOp(arraySort), result, indexTerm, 
                       shadowNumber);
        } else {
            result = tf.createArrayTerm(ArrayOp.getArrayOp(arraySort), result, indexTerm);
        }  
    }            
    ;exception
        catch [TermCreationException ex] {
              semanticError(ex.getMessage());
        }



accesstermlist returns [HashSet accessTerms = new HashSet()] {Term t = null;}:
     (t=accessterm {accessTerms.add(t);} ( COMMA t=accessterm {accessTerms.add(t);})* )? ;


term130 returns [Term a = null]
    :
        {isMetaOperator()}? a = specialTerm
    |   a = funcpredvarterm
    |   LPAREN a = term RPAREN 
    |   "true"  { a = tf.createJunctorTerm(Op.TRUE); }
    |   "false" { a = tf.createJunctorTerm(Op.FALSE); }
    |   a = ifThenElseTerm
    |   a = ifExThenElseTerm
    //Used for OCL Simplification.
    //WATCHOUT: Woj: some time we will need to have support for strings in Java DL too,
    // what then? This here is specific to OCL, isn't it?
    |   literal:STRING_LITERAL
        {
            String s = literal.getText(); 
            Name name = new Name(s);
            TermSymbol stringLit = (TermSymbol)functions().lookup(name);
            if (stringLit == null) {
                stringLit = new RigidFunction(name, 
                        OclSort.STRING, new Sort[0]);
                addFunction((Function)stringLit);
            }
            a = tf.createFunctionTerm(stringLit);
        }
   ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }


abbreviation returns [Term a=null]
{ 
    String sc = null;
}
    :
        (   sc = simple_ident
            {
                a =  scm.getTerm(sc);
                if(a==null){
                    throw new NotDeclException
                        ("abbreviation", sc, 
                         getFilename(), getLine(), getColumn());
                }                                
            }
        )
    ;

ifThenElseTerm returns [Term result = null]
{
    Term condF, thenT, elseT;
}
    :
        IF LPAREN condF = term RPAREN
        {
            if (condF.sort() != Sort.FORMULA) {
                semanticError
		  ("Condition of an \\if-then-else term has to be a formula.");
            }
        }
        THEN LPAREN thenT = term RPAREN
        ELSE LPAREN elseT = term RPAREN
        {
            result = tf.createIfThenElseTerm ( condF, thenT, elseT );
        }
 ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

ifExThenElseTerm returns [Term result = null]
{
    Term condF, thenT, elseT;
    ListOfQuantifiableVariable exVars = SLListOfQuantifiableVariable.EMPTY_LIST;
    ArrayOfQuantifiableVariable exVarsAr = null;
}
    :
        IFEX exVars = bound_variables
               {
                    exVarsAr = new ArrayOfQuantifiableVariable
                                           ( exVars.toArray () );
               }
        LPAREN condF = term RPAREN
        {
            if (condF.sort() != Sort.FORMULA) {
                semanticError
		  ("Condition of an \\if-then-else term has to be a formula.");
            }
        }
        THEN LPAREN thenT = term RPAREN
        {
            while ( !exVars.isEmpty () ) {
                if(!isGlobalDeclTermParser())
                    unbindVars ();
                exVars = exVars.tail ();
            }
        }
        ELSE LPAREN elseT = term RPAREN
        {
            result = tf.createIfExThenElseTerm ( exVarsAr, condF, thenT, elseT );
        }
 ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }


//"TermWithBoundVars" is used here instead of "Term" to allow for
//syntax needed for OCL simplification.

argument returns [TermWithBoundVars p = null]
{
    ArrayOfQuantifiableVariable vars = null;
    Term a;
}
:
 (vars = ocl_bound_variables)? 
 (
   // WATCHOUT Woj: can (should) this be unified to term60?
   {isTermParser() || isGlobalDeclTermParser()}? 
     a = term 
  |  
     a = term60 
 )
 {
   p = new TermWithBoundVars(vars, a);
    if(vars != null && !isGlobalDeclTermParser() )
       unbindVars();
 }
 ;
  
ocl_bound_variables returns [ArrayOfQuantifiableVariable vars = null] 
{
   ListOfQuantifiableVariable vs = null;
}
:
  BIND vs = bound_variables {
     vars = new ArrayOfQuantifiableVariable(vs.toArray());
  }
 ;

quantifierterm returns [Term a = null]
{
    Operator op = null;
    ListOfQuantifiableVariable vs = null;
    Term a1 = null;
}
:
        (   FORALL { op = Op.ALL; }
          | EXISTS  { op = Op.EX;  })
        vs = bound_variables a1 = term60
        {
            a = tf.createQuantifierTerm((Quantifier)op,
	       new ArrayOfQuantifiableVariable(vs.toArray()),a1);
            if(!isGlobalDeclTermParser())
              unbindVars();
        }
;

//term120_2
update_or_substitution returns [Term result = null]
:
      (LBRACE SUBST) => 
	 result = substitutionterm
      |  (
           {isGlobalDeclTermParser()}? result = simple_updateterm
	 |
           result = updateterm
       )
    ; 

substitutionterm returns [Term result = null] 
{
  QuantifiableVariable v = null;
  SubstOp op = Op.SUBST;
  Term a1 = null;
  Term a2 = null;
}
:
   LBRACE SUBST
     v = one_bound_variable SEMI
     { // Tricky part, v cannot be bound while parsing a1
       if(!isGlobalDeclTermParser())
          unbindVars();
     }
     a1=logicTermReEntry
     { // The rest of the tricky part, bind it again
       if(!isGlobalDeclTermParser())
          if(v instanceof LogicVariable)
            bindVar((LogicVariable)v);
	  else
	    bindVar();
     }
   RBRACE
   ( a2 = term110 | a2 = unary_formula ) {
      result = tf.createSubstitutionTerm ( op, v, a1, a2 );
      if(!isGlobalDeclTermParser())
        unbindVars();
   }
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

simple_updateterm returns [Term a = null]
{
  ParsableVariable v;
  Term a1, a2;
}
:
  LBRACE v = varId ASSIGN a1=term RBRACE ( a2 = term110 | a2 = unary_formula )
  { 
	a = tf.createUpdateTerm ( tf.createVariableTerm ( (ProgramVariable) v ), a1, a2 );
  }
;

updateterm returns [Term result = null] 
{ 
    SingleUpdateData sud = null;
    List locations = new LinkedList();
    List values    = new LinkedList();
    List guards    = new LinkedList();
    List boundVars = new LinkedList();
    Term a2 = null;
} :
        LBRACE ((STAR ASSIGN)=> 
          (STAR ASSIGN STAR
             num:NUM_LITERAL RBRACE ( a2 = term110 | a2 = unary_formula ) {
                return tf.createAnonymousUpdateTerm
                   (new Name("*:=*"+num.getText()), a2);
             }                  
          )	  
          | 
          (sud = singleupdate {
            locations.add(sud.a0); 
            values.add(sud.a1); 
            guards.add(sud.guard);
            boundVars.add(sud.boundVars);
          } (  ( COMMA {  
                 	System.err.println(getFilename() + "(" + getLine() + 
                 	", " + getColumn() + "): " + "The comma ',' " + 
                 	"for parallel composition of updates is deprecated and " + 
                 	"will be skipped in future. Please use '||' instead.");
                 } | PARALLEL)
                 
                sud = singleupdate {
                locations.add(sud.a0); 
                values.add(sud.a1); 
                guards.add(sud.guard);
                boundVars.add(sud.boundVars);
          })*) RBRACE ( a2 = term110 | a2 = unary_formula )
        {   

            result = tf.createQuanUpdateTerm
		((ArrayOfQuantifiableVariable[])boundVars.toArray
                     (new ArrayOfQuantifiableVariable[boundVars.size()]),
		 (Term[])guards.toArray(new Term[guards.size()]),
		 (Term[])locations.toArray(new Term[locations.size()]),
		 (Term[])values.toArray(new Term[values.size()]),
		  a2);
        })
   ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

singleupdate returns[SingleUpdateData sud=null]
{
    Term a0 = null;
    Term a1 = null;
    Term phi = null;
    ListOfQuantifiableVariable boundVars = SLListOfQuantifiableVariable.EMPTY_LIST;
    sud = new SingleUpdateData();
}  :
        (
            FOR boundVars = bound_variables
                   {
                        sud.boundVars = new ArrayOfQuantifiableVariable
                                               ( boundVars.toArray () );
                   }
        ) ?
        (
            (IF) => (
                IF
                LPAREN
                phi=term
                {
                    if (phi.sort() != Sort.FORMULA) {
                      semanticError("Guard of an update has to be a formula.");
                    }
                    sud.guard = phi;
                }
                RPAREN
            ) | (
                // nothing
            )
        )
        (a0 = lhsSingle ) ASSIGN (a1 = rhsSingle) {
            sud.a0 = a0;
            sud.a1 = a1;
            while ( !boundVars.isEmpty () ) {
                unbindVars ();
                boundVars = boundVars.tail ();
            }
        }
    ;
   
bound_variables returns[ListOfQuantifiableVariable list = SLListOfQuantifiableVariable.EMPTY_LIST]
{
  QuantifiableVariable var = null;
}
:
      LPAREN
        var = one_bound_variable { list = list.append(var); }
       (SEMI var = one_bound_variable { list = list.append(var); })*
      RPAREN
   | var = one_bound_variable { list = list.append(var); } SEMI 
     
;

one_bound_variable returns[QuantifiableVariable v=null]
:
  {isGlobalDeclTermParser()}? v = one_logic_bound_variable_nosort
 |
  {inSchemaMode()}? v = one_schema_bound_variable
 |
  {!inSchemaMode()}? v = one_logic_bound_variable
;

one_schema_bound_variable returns[QuantifiableVariable v=null]
{
  String id = null;
  TermSymbol ts = null;
}
:
   id = simple_ident {
      ts = (TermSymbol) variables().lookup(new Name(id));   
      // It is my belief (Woj) that this check is obsolete
      // if ( ts == null || ts instanceof LogicVariable ) {
      //  throw new KeYSemanticException("Quantified variables need a sort.", 
      //          getFilename(), getLine(), getColumn());
      // }
      if ( ! (ts instanceof SchemaVariable && ((SchemaVariable)ts).isVariableSV())) {
        semanticError(ts+" is not allowed in a quantifier.");
      }
      v = (SortedSchemaVariable) ts;
      bindVar();
   }
;

one_logic_bound_variable returns[QuantifiableVariable v=null]
{ 
  Sort s = null;
  String id = null;
}
:
  s=sortId id=simple_ident {
    v = bindVar(id, s);
  }
;

one_logic_bound_variable_nosort returns[QuantifiableVariable v=null]
{ 
  String id = null;
}
:
  id=simple_ident {
    v = (LogicVariable)variables().lookup(new Name(id));
  }
;

rhsSingle returns[Term result = null]
{} :
        result = logicTermReEntry
    ;

lhsSingle returns[Term result = null]
 :
        result = logicTermReEntry
        { 
            if (!(result.sort() instanceof ProgramSVSort ||
                  result.op() instanceof de.uka.ilkd.key.logic.op.Location))  {
                semanticError("Only locations can be updated, but " + 
                	result.op() + " is no location, but a " + 
                	result.op().getClass().getName());
            }
        }
    ;

modality_dl_term returns [Term a = null]
{
    Term a1;
    PairOfTermArrayAndBoundVarsArray argsWithBoundVars = null;
    Term[] terms = null;
    Operator op = null;
    PairOfStringAndJavaBlock sjb = null;
}
   :
   modality : MODALITY
     {
       sjb=getJavaBlock(modality);
       Debug.out("op: ", sjb.opName);
       Debug.out("program: ", sjb.javaBlock);
       if(sjb.opName.charAt(0) == '#') {
         if (!inSchemaMode()) {
           semanticError
             ("No schema elements allowed outside taclet declarations ("+sjb.opName+")");
         }
         op = (SchemaVariable)variables().lookup(new Name(sjb.opName));
       } else {
         op = Op.getModality(sjb.opName);
       }
       if(op == null) {
         semanticError("Unknown modal operator: "+sjb.opName);
       }
       bindProgVars(progVars(sjb.javaBlock));
     }
   // CAREFUL here, op can be null during guessing stage (use lazy &&)
   ({op != null && op.arity() == 1}? a1=term60
     // This here will accept both (1) \modality...\endmodality post and
     // (2) \modality...\endmodality(post)
     // so that it is consistent with pretty printer that prints (1).
     // A term "(post)" seems to be parsed as "post" anyway
      {
            a = tf.createProgramTerm(op, sjb.javaBlock, new Term[]{a1});
            unbindProgVars();
      }
    |
    argsWithBoundVars = argument_list
      {
        Debug.fail("We don't have modalities with arity > 1, so this should not	be executed.");
        unbindProgVars();
        if (argsWithBoundVars != null) {
          terms = argsWithBoundVars.getTerms();
        }
        if(op.arity() != terms.length) {
            semanticError("The arity of " + op.name() +
                " is "+op.arity() + ", but you provided " + terms.length + " arguments");
        }
        a = tf.createProgramTerm(op, sjb.javaBlock, terms);
      }
   )
   ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

//"PairOfTermArrayAndBoundVarsArray" is used here instead of "Term" to allow for
//syntax needed for OCL simplification.
argument_list returns [PairOfTermArrayAndBoundVarsArray ts = null]
{
    List args = new LinkedList();
    TermWithBoundVars p1, p2;
}
    :
        LPAREN 
        (p1 = argument { args.add(p1);  }

            (COMMA p2 = argument { args.add(p2); } )* )?

        RPAREN
        {
            ts = new PairOfTermArrayAndBoundVarsArray(args);
        }

    ;

funcpredvarterm returns [Term a = null]
{
    List dependencyListList = null;
    PairOfTermArrayAndBoundVarsArray argsWithBoundVars = null;
    String varfuncid;
    String neg = "";
    boolean opSV = false;
}
    :
        ch:CHAR_LITERAL {
            String s = ch.getText();
            int intVal = 0;
            if (s.length()==3) {
                intVal = (int)s.charAt(1);
            } else {
                try {
                    intVal = Integer.parseInt(s.substring(3,s.length()-1),16);
                } catch (NumberFormatException ex) {
                    semanticError("'"+s+"' is not a valid character.");
                }       
            }
            a = tf.createFunctionTerm((Function) functions().lookup(new Name("C")), 
                                      toZNotation(""+intVal, functions(), tf).sub(0));
        }
    | 
        ((MINUS)? NUM_LITERAL) => (MINUS {neg = "-";})? number:NUM_LITERAL
        { a = toZNotation(neg+number.getText(), functions(), tf);}    
    | AT a = abbreviation
    | varfuncid = funcpred_name 
        (   (LBRACKET dependency_list_list RBRACKET) =>
            (
                LBRACKET
                dependencyListList = dependency_list_list
                RBRACKET
                {
                    varfuncid
                        = KeYParser.createDependencyName(varfuncid,
                                                         dependencyListList);
                }
            )
        )?
	((LPAREN)=>argsWithBoundVars = argument_list)? 
        //argsWithBoundVars==null indicates no argument list
        //argsWithBoundVars.size()==0 indicates open-close-parens ()
        {  
            Operator op = lookupVarfuncId(varfuncid, argsWithBoundVars);            
            if (op instanceof ParsableVariable) {
                a = termForParsedVariable((ParsableVariable)op);
            } else  if (op instanceof TermSymbol) {
                if (argsWithBoundVars==null) {
                    argsWithBoundVars = new PairOfTermArrayAndBoundVarsArray(new LinkedList());
                }

                a = tf.createFunctionWithBoundVarsTerm((TermSymbol)op, argsWithBoundVars);

            }
        }
; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

specialTerm returns [Term result = null] 
{
    Operator vf = null;
}:
        vf = expr_op 
            {   
                result = tf.createFunctionTerm((Function)vf, AN_ARRAY_OF_TERMS);
            }                 
     | 
     {isTacletParser() || isProblemParser()}?
       result = metaTerm
   ; exception
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

arith_op returns [String op = null]
:
    PERCENT {op = "%";}
  | STAR {op = "*";}
  | MINUS {op = "-";}
  | SLASH {op = "/";}
  | PLUS { op = "+";}
;

expr_op returns [Operator v = null] 
{
    ParsableVariable left_var0 = null;
    ParsableVariable right_var0 = null;
    ParsableVariable unary_var0 = null;
    String op_str = null;
}   
    :

        IN_TYPE LPAREN (
	    (left_var0=varId (op_str = arith_op right_var0 = varId)?)
	  |
            ( MINUS unary_var0 = varId) 
        ) RPAREN
        {  
            if (unary_var0!=null) {
                // can only be unary minus
                ProgramSV unary_var = (ProgramSV) unary_var0;
                Sort type = de.uka.ilkd.key.logic.sort.Sort.FORMULA;
                return new InTypeOperator
                    (type, new de.uka.ilkd.key.java.expression.operator.Negative(unary_var));
            }
            else {
                ProgramSV left_var = (ProgramSV) left_var0;
                Sort type = de.uka.ilkd.key.logic.sort.Sort.FORMULA;
                if (right_var0 != null) {
                    ProgramSV right_var = (ProgramSV) right_var0;
                    if ("+".equals(op_str)) {
                        return new InTypeOperator
                            (type, new de.uka.ilkd.key.java.expression.operator.Plus(left_var, right_var));
                    } else if ("-".equals(op_str)) {
                        return new InTypeOperator
                            (type, new de.uka.ilkd.key.java.expression.operator.Minus(left_var, right_var));
                    } else if ("*".equals(op_str)) {
                        return new InTypeOperator
                            (type, new de.uka.ilkd.key.java.expression.operator.Times(left_var, right_var));
                    } else if ("/".equals(op_str)) {
                        return new InTypeOperator
                            (type, new de.uka.ilkd.key.java.expression.operator.Divide(left_var, right_var));
                    } else if ("%".equals(op_str)) {
                        return new InTypeOperator
                            (type, new de.uka.ilkd.key.java.expression.operator.Modulo(left_var, right_var));
                    } 
                }
                else {
                    return new InTypeOperator(type, left_var);
                }
            }
        }
    ;

varId returns [ParsableVariable v = null]
    :
        id:IDENT 
        {   
            v = (ParsableVariable) variables().lookup(new Name(id.getText()));
            if (v == null) {
                throw new NotDeclException("variable", id, 
                                           getFilename());
            }
        } 
  ;

varIds returns [LinkedList list = new LinkedList()]
{
   ListOfString ids = null;
   ParsableVariable v = null;
   String id = null;
}
    :
      ids = simple_ident_comma_list {
         IteratorOfString it = ids.iterator();
	 while(it.hasNext()) {
	    id = it.next();
            v = (ParsableVariable) variables().lookup(new Name(id));
            if (v == null) {
               semanticError("Variable " +id + " not declared.");
            }
	    list.add(v);
	 }
      }
  ;

taclet[SetOfChoice choices] returns [Taclet r] 
{ 
    Sequent ifSeq = Sequent.EMPTY_SEQUENT;
    Object  find = null;
    r = null;
    TacletBuilder b = null;
    int stateRestriction = RewriteTaclet.NONE;
}
    : 
        name:IDENT (choices=option_list[choices])? 
        LBRACE {
	  //  schema var decls
	  namespaces().setVariables(new Namespace(variables()));
        } 
	( SCHEMAVAR one_schema_var_decl ) *
        ( ASSUMES LPAREN ifSeq=seq RPAREN ) ?
        ( FIND {parsingFind = true; } LPAREN find = termorseq RPAREN {parsingFind = false;}
            ( SAMEUPDATELEVEL { stateRestriction = RewriteTaclet.SAME_UPDATE_LEVEL; } |
              INSEQUENTSTATE { stateRestriction = RewriteTaclet.IN_SEQUENT_STATE; } 
            ) ? ) ?
        { 
            b = createTacletBuilderFor(find, stateRestriction);
            b.setName(new Name(name.getText()));
            b.setIfSequent(ifSeq);
        }
        ( VARCOND LPAREN varexplist[b] RPAREN ) ?
        goalspecs[b]
        modifiers[b]
        RBRACE
        { 
            b.setChoices(choices);
            r = b.getTaclet(); 
            taclet2Builder.put(r,b);
	  // dump local schema var decls
	  namespaces().setVariables(variables().parent());
        }
    ;

modifiers[TacletBuilder b]
{
  Vector rs = null;
  String dname= null;
  String oname= null;
  String htext = null;
} : 
        ( rs = rulesets {
           Iterator it = rs.iterator();
           while(it.hasNext())
               b.addRuleSet((RuleSet)it.next());
         }
        | NONINTERACTIVE { 
                //      b.setNoninteractive(true);  
                // "noninteractive" (as it is now) is confusing
                // dropped this completely until a better solution (->Uwe)
            }       
        | DISPLAYNAME dname = string_literal 
            {b.setDisplayName(dname);}
        | OLDNAME oname = string_literal 
            {b.addOldName(oname);}
        | HELPTEXT htext = string_literal
            {b.setHelpText(htext);}
        ) *
    ;

seq returns [Sequent s] {Semisequent ant,suc; s = null; } : 
        ant=semisequent SEQARROW suc=semisequent 
        { s = Sequent.createSequent(ant, suc); }
    ;
exception
     catch [RuntimeException ex] {
         keh.reportException
  	    (new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
     }
termorseq returns [Object o]
{
    Term head = null;
    Sequent s = null;
    Semisequent ss = null;
    o = null; 
}
    :
        head=term ( COMMA s=seq | SEQARROW ss=semisequent ) ?
        {
            if ( s == null ) {
                if ( ss == null ) {
                    // Just a term
                    o = head;
                } else {
                    // A sequent with only head in the antecedent.
                    Semisequent ant = Semisequent.EMPTY_SEMISEQUENT;
                    ant = ant.insertFirst(
                                          new ConstrainedFormula(head, Constraint.BOTTOM)).semisequent();
                    o = Sequent.createSequent(ant,ss);
                }
            } else {
                // A sequent.  Prepend head to the antecedent.
                Semisequent newAnt = s.antecedent();
                newAnt = newAnt .insertFirst(
                                             new ConstrainedFormula(head, Constraint.BOTTOM)).semisequent();
                o = Sequent.createSequent(newAnt,s.succedent());
            }
        }
    |
        SEQARROW ss=semisequent
        {
            o = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,ss);
        }
    ;

semisequent returns [Semisequent ss]
{ 
    Term head = null;
    ss = Semisequent.EMPTY_SEMISEQUENT; 
}
    :
        /* empty */ | 
        head=term ( COMMA ss=semisequent ) ? 
        { ss = ss.insertFirst(new ConstrainedFormula(head, Constraint.BOTTOM)).semisequent(); }
    ;

varexplist[TacletBuilder b] : varexp[b] ( COMMA varexp[b] ) * ;

varexp[TacletBuilder b]
{
  boolean negated = false;
}
:
  (   varcond_new[b]  | varcond_newlabel[b]
    | varcond_free[b] | varcond_literal[b]
    | varcond_hassort[b] | varcond_query[b]
    | varcond_non_implicit[b] | varcond_non_implicit_query[b]
    | varcond_enum_const[b]
    | varcond_inReachableState[b] 
  ) 
  | 
  ( (NOT {negated = true;} )? 
      ( varcond_reference[b, negated] 
      | varcond_enumtype[b, negated]
      | varcond_staticmethod[b,negated]  
      | varcond_referencearray[b, negated]
      | varcond_array[b, negated]
      | varcond_abstractOrInterface[b, negated]
      | varcond_static[b,negated] 
      | varcond_typecheck[b, negated]
      | varcond_localvariable[b, negated]
	  | varcond_isupdated[b, negated]
      | varcond_freeLabelIn[b,negated] )
  )
;

type_resolver returns [TypeResolver tr = null] 
{
    Sort s = null;
    ParsableVariable y = null;
} :
    s = any_sortId_check[true]      
    {
        if ( !( s instanceof GenericSort ) ) {
        throw new GenericSortException ( "sort",
            "Generic sort expected", s,
            getFilename (), getLine (), getColumn () );
        }
        tr = TypeResolver.createGenericSortResolver((GenericSort)s);
    } |
    ( TYPEOF LPAREN y = varId RPAREN  
        {  tr = TypeResolver.createElementTypeResolver((SchemaVariable)y); } )
    |
    ( CONTAINERTYPE LPAREN y = varId RPAREN  
        {  tr = TypeResolver.createContainerTypeResolver((SchemaVariable)y); } )
;

varcond_new [TacletBuilder b]
{
  ParsableVariable x = null, y = null;
  Sort s = null;
}
:
   NEW LPAREN x=varId COMMA
      (
          TYPEOF LPAREN y=varId RPAREN {
	    b.addVarsNew((SchemaVariable) x, (SchemaVariable) y, false);
	  }
      |
          ELEMTYPEOF LPAREN y=varId RPAREN {
 	    b.addVarsNew((SchemaVariable) x, (SchemaVariable) y, true);
	  }
      |
         DEPENDINGON LPAREN y=varId RPAREN {
	    b.addVarsNewDependingOn((SchemaVariable)x,(SchemaVariable)y);
	  }
      |  DEPENDINGONMOD LPAREN y=varId RPAREN {
          b.addVariableCondition(new NewDepOnAnonUpdates((SchemaVariable) x,(SchemaVariable)y));		  
	  }
      | s=sortId_check[true] {
		b.addVarsNew((SchemaVariable) x, s);
	  }
      )
   RPAREN
   
;

varcond_newlabel [TacletBuilder b] 
{ 
  ParsableVariable x;
}
:
  NEWLABEL LPAREN x=varId RPAREN {
     b.addVariableCondition(new NewJumpLabelCondition((SchemaVariable)x));
  }
;
varcond_typecheck [TacletBuilder b, boolean negated]
{
  TypeResolver fst = null, snd = null;
  int typecheckType = -1;
}
:
   (  SAME  { 	
	typecheckType = negated ? TypeComparisionCondition.NOT_SAME : TypeComparisionCondition.SAME;
	} 
    | COMPATIBLE { 
      typecheckType = TypeComparisionCondition.NOT_COMPATIBLE;
	if (!negated) {  
	  semanticError("Compatible types condition only available as negated version.");
	} 
      }
    | ISSUBTYPE { typecheckType = negated ?  
	  TypeComparisionCondition.NOT_IS_SUBTYPE: TypeComparisionCondition.IS_SUBTYPE; 
      }
    | STRICT ISSUBTYPE {
         if (negated) {  
	  semanticError("A negated strict subtype check does not make sense.");
	} 
	typecheckType = TypeComparisionCondition.STRICT_SUBTYPE;
      }
   ) 
   LPAREN fst = type_resolver COMMA snd = type_resolver RPAREN {
               b.addVariableCondition
                 (new TypeComparisionCondition(fst, snd, typecheckType));
            }
;


varcond_free [TacletBuilder b]
{
  ParsableVariable x = null;
  LinkedList ys = null;
}
:
   NOTFREEIN LPAREN x=varId COMMA ys=varIds RPAREN {
     Iterator it = ys.iterator();
     while(it.hasNext()) {
        b.addVarsNotFreeIn((SchemaVariable)x,(SchemaVariable)it.next());
     }
   }
;

varcond_literal [TacletBuilder b]
{
  ParsableVariable x = null, y = null;
}
:
   NOTSAMELITERAL LPAREN x=varId COMMA y=varId RPAREN {
     b.addVariableCondition(new TestLiteral(
       (SchemaVariable) x, (SchemaVariable) y));          
   }
;



varcond_hassort [TacletBuilder b]
{
  ParsableVariable x = null;
  Sort s = null;
}
:
   HASSORT LPAREN x=varId COMMA s=any_sortId_check[true] RPAREN {
     if ( !( s instanceof GenericSort ) )
   	 throw new GenericSortException ( "sort",
   					  "Generic sort expected", s,
   					   getFilename (), getLine (), getColumn () );
     if ( !JavaTypeToSortCondition. checkSortedSV((SchemaVariable)x) )
   	 semanticError("Expected schema variable of kind EXPRESSION or TYPE, " +
   					"but is " + x);
     b.addVariableCondition(new JavaTypeToSortCondition ((SchemaVariable)x, (GenericSort)s));
   }
;

varcond_enumtype [TacletBuilder b, boolean negated]
{
  TypeResolver tr = null;
}
:
   ISENUMTYPE LPAREN tr = type_resolver RPAREN
      {
         b.addVariableCondition(new EnumTypeCondition(tr, negated));
      }
;
 

varcond_reference [TacletBuilder b, boolean isPrimitive]
{
  ParsableVariable x = null;
  TypeResolver tr = null;
  String id = null;
  boolean nonNull = false;
}
:
   ISREFERENCE (LBRACKET 
                     id = simple_ident {                                          	
                   	if ("non_null".equals(id)) {
                   	    nonNull = true;
                   	} else {	   
                            semanticError(id + 
                   	      " is not an allowed modifier for the \\isReference variable condition.");
                   	}                   	
                     }
                RBRACKET)? 
   LPAREN      
        tr = type_resolver                           
   RPAREN 
   { b.addVariableCondition(new TypeCondition(tr, !isPrimitive, nonNull)); }
;

varcond_non_implicit [TacletBuilder b]
{
  ParsableVariable x = null;
}
:
   ISNONIMPLICIT LPAREN x=varId RPAREN {
     b.addVariableCondition(new NonImplicitTypeCondition((SchemaVariable) x));
   } 
;

varcond_query [TacletBuilder b]
{
  ParsableVariable x = null;
}
:
   ISQUERY LPAREN x=varId RPAREN {
     b.addVariableCondition(new TestQuery((SchemaVariable)x));
   }
;

varcond_inReachableState [TacletBuilder b]
{
  ParsableVariable x = null;
}
:
   ISINREACHABLESTATE LPAREN x=varId RPAREN    	
   {
      b.addVariableCondition(new InReachableStateCondition((SchemaVariable)x));
   }
;

varcond_non_implicit_query [TacletBuilder b]
{
  ParsableVariable x = null;
}
:
   ISNONIMPLICITQUERY LPAREN x=varId RPAREN 
        {
            b.addVariableCondition(new TestNonImplicitQuery((SchemaVariable)x));
        }
    ;

/*varcond_monomials [TacletBuilder b]
{
  ParsableVariable x = null, y = null;
}
:
   MONOMIALSDIVIDE LPAREN x=varId COMMA y=varId RPAREN {
     final VariableCondition c;
     c = new MonomialsDivideCondition
                  ((SchemaVariable)x,(SchemaVariable)y);
     b.addVariableCondition ( c );
   }
;*/
         
varcond_staticmethod [TacletBuilder b, boolean negated]
{
  ParsableVariable x = null, y = null, z = null;
}
:
   STATICMETHODREFERENCE LPAREN x=varId COMMA y=varId COMMA z=varId RPAREN {
      b.addVariableCondition(new StaticMethodCondition
         (negated, (SchemaVariable)x, (SchemaVariable)y, (SchemaVariable)z));
   }
;

varcond_referencearray [TacletBuilder b, boolean primitiveElementType]
{
  ParsableVariable x = null;
}
:
   ISREFERENCEARRAY LPAREN x=varId RPAREN {
     b.addVariableCondition(new ArrayComponentTypeCondition(
       (SchemaVariable)x, !primitiveElementType));
   }
;

varcond_array [TacletBuilder b, boolean negated]
{
  ParsableVariable x = null;
}
:
   ISARRAY LPAREN x=varId RPAREN {
     b.addVariableCondition(new ArrayTypeCondition(
       (SchemaVariable)x, negated));
   }
;


varcond_abstractOrInterface [TacletBuilder b, boolean negated]
{
  TypeResolver tr = null;
}
:
   IS_ABSTRACT_OR_INTERFACE LPAREN tr=type_resolver RPAREN {
     b.addVariableCondition(new AbstractOrInterfaceType(tr, negated));
   }
;

varcond_enum_const [TacletBuilder b]
{
  ParsableVariable x = null;
}
:
   ENUM_CONST LPAREN x=varId RPAREN {
      b.addVariableCondition(new EnumConstantCondition(
	(SchemaVariable) x));     
   }
;

varcond_static [TacletBuilder b, boolean negated]
{
  ParsableVariable x = null;
}
:
   STATIC LPAREN x=varId RPAREN {
      b.addVariableCondition(new StaticReferenceCondition(
	(SchemaVariable) x, negated));     
   }
;

varcond_localvariable [TacletBuilder b, boolean negated]
{
  ParsableVariable x = null;
}
:
   ISLOCALVARIABLE 
	LPAREN x=varId RPAREN {
     	   b.addVariableCondition(new LocalVariableCondition((SchemaVariable) x, negated));
        } 
;

varcond_isupdated [TacletBuilder b, boolean negated]
{
  ParsableVariable x = null;
}
:
   ISUPDATED 
	LPAREN x=varId RPAREN {
     	   b.addVariableCondition(new IsUpdatedVariableCondition((SchemaVariable) x, negated));
        } 
;


varcond_freeLabelIn [TacletBuilder b, boolean negated]
{
   ParsableVariable label = null, statement = null;
} :

 FREELABELIN 
    LPAREN label=varId COMMA statement=varId RPAREN {
    	b.addVariableCondition(new FreeLabelInVariableCondition((SchemaVariable) label, 
    	(SchemaVariable) statement, negated ));
    }
;

goalspecs[TacletBuilder b] :
        CLOSEGOAL
    | goalspecwithoption[b] ( SEMI goalspecwithoption[b] )* ;

goalspecwithoption[TacletBuilder b]
{
    SetOfChoice soc = SetAsListOfChoice.EMPTY_SET;
} :
        (( soc = option_list[soc]
                LBRACE
                goalspec[b,soc] 
                RBRACE)
        |  
            goalspec[b,null] 
        )
    ;

option returns [Choice c=null]
:
        cat:IDENT COLON choice:IDENT
        {
            c = (Choice) choices().lookup(new Name(cat.getText()+":"+choice.getText()));
            if(c==null) {
                throw new NotDeclException
			("Option", choice, getFilename());
	    }
        }
    ;
    
option_list[SetOfChoice soc] returns [SetOfChoice result = null]
{
   Choice c = null;
}
:
LPAREN {result = soc; } 
  c = option {result = result.add(c);}
  (COMMA c = option {result = result.add(c);})*
RPAREN
;

goalspec[TacletBuilder b, SetOfChoice soc] 
{
    Object rwObj = null;
    Sequent addSeq = Sequent.EMPTY_SEQUENT;
    ListOfTaclet addRList = SLListOfTaclet.EMPTY_LIST;
    SetOfSchemaVariable addpv = SetAsListOfSchemaVariable.EMPTY_SET;
    String name = null;
}
    :
        (name = string_literal COLON)?
        (   ( rwObj = replacewith
                (addSeq=add)? 
                (addRList=addrules)? 
                (addpv=addprogvar)?
            )
        | ( addSeq=add (addRList=addrules)? )
        | ( addRList=addrules )
        )
        {
            addGoalTemplate(b,name,rwObj,addSeq,addRList,addpv,soc);
        }
        
    ;

replacewith returns [Object o] { o = null; } :
        REPLACEWITH LPAREN o=termorseq RPAREN;

add returns [Sequent s] { s = null;} :
        ADD LPAREN s=seq RPAREN;

addrules returns [ListOfTaclet lor] { lor = null; } :
        ADDRULES LPAREN lor=tacletlist RPAREN;

addprogvar returns [SetOfSchemaVariable pvs] {pvs = null; } :
        ADDPROGVARS LPAREN pvs=pvset RPAREN;

tacletlist returns [ListOfTaclet lor]
{ 
    Taclet head = null;
    lor = SLListOfTaclet.EMPTY_LIST; 
}
    :
        head=taclet[SetAsListOfChoice.EMPTY_SET]   
        ( /*empty*/ | COMMA lor=tacletlist ) { lor = lor.prepend(head); }
    ;

pvset returns [SetOfSchemaVariable pvs] 
{
    ParsableVariable pv = null;
    pvs = SetAsListOfSchemaVariable.EMPTY_SET;
}
    :
        pv=varId
        ( /*empty*/ | COMMA pvs=pvset ) { pvs = pvs.add
                                          ((SchemaVariable)pv); };

rulesets returns [Vector rs = new Vector()] :
        HEURISTICS LPAREN ruleset[rs] ( COMMA ruleset[rs] ) * RPAREN ;

ruleset[Vector rs]
:
        id:IDENT
        {   
            RuleSet h = (RuleSet) ruleSets().lookup(new Name(id.getText()));
            if (h == null) {
                throw new NotDeclException("ruleset", id, getFilename());
            }
            rs.add(h);
        }
    ;

metaId returns [MetaOperator v = null] 
{
  String id = null;
}
:
  id = simple_ident {
     v = AbstractMetaOperator.name2metaop(id);
     if (v == null)
       semanticError("Unknown metaoperator: "+id);
  }
;

metaTerm returns [Term result = null]
{
    LinkedList al = new LinkedList();
    String param = null;
    MetaOperator vf = null;
    Term t = null;
} 
    :
        (vf = metaId (COLON param = simple_ident)? 
           ( LPAREN 
            t = term
            {
                al.add(t);
            }
            ( COMMA 
                t = term
                {
                    al.add(t);
                }   
            )* RPAREN )?
            {   
	        if(param != null) {
		  MetaOperator nvf = vf.getParamMetaOperator(param);
		  if(nvf == null) {
                    semanticError("Meta operator "+vf.name()+" is not a parametric meta operator.");
		  }else {
		    vf = nvf;
		  }
		}
                result = tf.createMetaTerm(vf,
                                           (Term[])al.toArray(AN_ARRAY_OF_TERMS));
            }         
        ) 
 ; exception
     catch [TermCreationException ex] {
         keh.reportException
  	    (new KeYSemanticException
			(ex.getMessage(), getFilename(), getLine(), getColumn()));
        }

contracts[SetOfChoice choices, Namespace funcNSForSelectedChoices]
{
  Choice c = null;
}
:
   CONTRACTS
       LBRACE {
	    switchToNormalMode();
	    IteratorOfChoice it = choices.iterator();
	    Namespace funcNSForRules = funcNSForSelectedChoices;
	    while(it.hasNext()){
		c=it.next();
		funcNSForRules = 
		    funcNSForRules.extended(c.funcNS().allElements());
	    }
	    namespaces().setFunctions(funcNSForRules); 
	    parsingContracts = true;
       }
       ( one_contract )*
       RBRACE {
            parsingContracts = false;
       }
;

one_contract 
{
  Term fma = null;
  SetOfLocationDescriptor modifiesClause = SetAsListOfLocationDescriptor.EMPTY_SET;
  String displayName = null;
  String contractName = null;
  Vector rs = null;
  NamespaceSet oldServicesNamespaces = null;
}
:
   contractName = simple_ident LBRACE { 
        //  program variable declarations and
        // add @pre functions
        namespaces().setProgramVariables(new AtPreNamespace(programVariables(), getJavaInfo()));    
        namespaces().setFunctions(new AtPreNamespace(functions(), getJavaInfo()));
        oldServicesNamespaces = getServices().getNamespaces(); //why are the Services namespaces
                                                             //not directly updated in the parser?
        getServices().setNamespaces(namespaces());
     }
     (prog_var_decls)? 
     fma = formula MODIFIES (modifiesClause = location_list)?
     (rs=rulesets)?   // for backward compatibility
     (DISPLAYNAME displayName = string_literal)?
     {
       DLSpecFactory dsf = new DLSpecFactory(getServices());
       try {
         contracts = contracts.add(dsf.createDLOperationContract(contractName,
	       					                 displayName,
       					                         fma, 
           				                         modifiesClause));
       } catch(ProofInputException e) {
         semanticError(e.getMessage());
       }
     } RBRACE SEMI {
     // dump local program variable declarations and @pre functions
     namespaces().setProgramVariables(programVariables().parent());
     namespaces().setFunctions(functions().parent());
     getServices().setNamespaces(oldServicesNamespaces);
   }
;

problem returns [ Term a = null ]
{
    Taclet s = null;
    SetOfChoice choices=SetAsListOfChoice.EMPTY_SET;
    Choice c = null;
    ListOfString stlist = null;
    Namespace funcNSForSelectedChoices = new Namespace();
    String pref = null;
}
    :


	{ if (capturer != null) capturer.mark(); }
        (pref = preferences)
        { if ((pref!=null) && (capturer != null)) capturer.mark(); }

        stlist = javaSource {
          if(stlist != null && stlist.size() > 1)
            Debug.fail("Don't know what to do with multiple java source entries.");
	    }
        
        decls
        { 
            if(parse_includes || onlyWith) return null;
            switchToNormalMode();
            IteratorOfChoice it = selectedChoices.iterator(); 
            while(it.hasNext()){
	         Choice choice = (Choice)choices().lookup(it.next().name());
		 if(choice != null) {
                   funcNSForSelectedChoices=funcNSForSelectedChoices.
                      extended(choice.funcNS().allElements());
	         }
             } 
             funcNSForSelectedChoices=funcNSForSelectedChoices.
                 extended(defaultChoice.
                          funcNS().allElements()); 
        }
        // WATCHOUT: choices is always going to be an empty set here,
	// isn't it?
	( contracts[choices, funcNSForSelectedChoices] )*
        (  RULES (choices = option_list[choices])?
	    LBRACE
            { 
                switchToSchemaMode(); 
                 IteratorOfChoice it = choices.iterator();
                 Namespace funcNSForRules = funcNSForSelectedChoices;
                 while(it.hasNext()){
                     c=it.next();
                     funcNSForRules = 
                         funcNSForRules.extended(c.funcNS().allElements());
                 }
                 namespaces().setFunctions(funcNSForRules); 
            }
            ( 
                s = taclet[choices] SEMI
                {
                    try {
                        if (!skip_taclets) {
                            taclets = taclets.addUnique(s);
                        }
                    } catch(de.uka.ilkd.key.collection.NotUniqueException e) {
                        semanticError
                        ("Cannot add taclet \"" + s.name() + 
                            "\" to rule base as a taclet with the same "+
                            "name already exists.");
                    }
                }
            )*
            RBRACE {choices=SetAsListOfChoice.EMPTY_SET;}
        ) *
        ((PROBLEM LBRACE 
            {switchToNormalMode(); 
	     namespaces().setFunctions(funcNSForSelectedChoices);
	     if (capturer != null) capturer.capture();}
                a = formula 
            RBRACE) | CHOOSECONTRACT {
	                if (capturer != null) capturer.capture();
	                chooseContract = true;
		      })?
        {
			setChoiceHelper(SetAsListOfChoice.EMPTY_SET, "");
        }
   ;

javaSource returns [ListOfString ids = SLListOfString.EMPTY_LIST]
{ 
  String s = null;
}
:
   (NOJAVAMODEL SEMI{ return null; } )
   |
   (JAVASOURCE 
      s = oneJavaSource { ids = ids.append(s); }
      (COMMA s = oneJavaSource { ids = ids.append(s); })*
    SEMI)?
    ;



oneJavaSource returns [String s = null]
{
  StringBuffer b=new StringBuffer();
  String l = null;
}
:
  (  l = string_literal {
       b.append(l);
     }
  |  
     SLASH { b.append("/"); }
  )+ {
    s = b.toString();
  }
;

preferences returns [String s = null]:
	( KEYSETTINGS LBRACE
		(s = string_literal)?
		RBRACE )?
	;
	
proof [ProblemLoader prl] :
        ( PROOF proofBody[prl] )?
    ;


proofBody [ProblemLoader prl] :
        LBRACE
            ( pseudosexpr[prl] )+ 
        RBRACE
    ;


pseudosexpr [ProblemLoader prl] { char eid='0'; String str = null; } :
        LPAREN (eid=expreid
            (str = string_literal { prl.beginExpr(eid,str); } )? 
            ( pseudosexpr[prl] )* ) ?
        { prl.endExpr(eid, stringLiteralLine); }
        RPAREN   
    ;

expreid returns [ char eid = '0' ]
{ String id = null; } 
:
   id = simple_ident {
      Character c = (Character)prooflabel2tag.get(id);
      if(c != null)
         eid = c.charValue();
   }
;
