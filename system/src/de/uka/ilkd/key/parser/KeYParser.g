// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

parser grammar KeYParser;

options {
    tokenVocab=KeYLexer;
    k = 1;
}

/* -*-antlr-*- */
@header {

  package de.uka.ilkd.key.parser;

  import de.uka.ilkd.key.parser.AmbigiousDeclException;
  import de.uka.ilkd.key.parser.GenericSortException;
  import de.uka.ilkd.key.parser.InvalidFindException;
  import de.uka.ilkd.key.parser.KeYSemanticException;
  import de.uka.ilkd.key.parser.NotDeclException;
  import de.uka.ilkd.key.parser.SchemaVariableModifierSet;
  import de.uka.ilkd.key.parser.UnfittingReplacewithException;
  import de.uka.ilkd.key.parser.ParserMode;
  import de.uka.ilkd.key.parser.DeclPicker;
  import de.uka.ilkd.key.parser.IdDeclaration;
  import de.uka.ilkd.key.parser.ParserConfig;

  import antlr.CharScanner;
  import antlr.SemanticException;
  import antlr.LexerSharedInputState;
  import antlr.TokenStreamException;
  import antlr.TokenStreamSelector;
  import org.antlr.runtime.*;

  import java.io.*;
  import java.util.HashSet;
  import java.util.Iterator;
  import java.util.LinkedHashMap;
  import java.util.LinkedHashSet;
  import java.util.LinkedList;
  import java.util.Set;
  import java.util.Vector;
  import java.math.BigInteger;

  import de.uka.ilkd.key.collection.*;
  import de.uka.ilkd.key.logic.*;
  import de.uka.ilkd.key.logic.op.*;
  import de.uka.ilkd.key.logic.sort.*;
  import de.uka.ilkd.key.logic.label.*;

  import de.uka.ilkd.key.proof.init.*;
  import de.uka.ilkd.key.proof.io.*;
  
  import de.uka.ilkd.key.rule.*;
  import de.uka.ilkd.key.rule.tacletbuilder.*;
  import de.uka.ilkd.key.rule.conditions.*;
  import de.uka.ilkd.key.rule.label.*;
 
  import de.uka.ilkd.key.speclang.*;

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

@annotateclass{ @SuppressWarnings("all") } 

@members{

    private static final Sort[] AN_ARRAY_OF_SORTS = new Sort[0];
    private static final Term[] AN_ARRAY_OF_TERMS = new Term[0];

    private static final int NORMAL_NONRIGID = 0;
    private static final int LOCATION_MODIFIER = 1;

    static HashMap<String, Character> prooflabel2tag = new LinkedHashMap<String, Character>(15);
    static {
      prooflabel2tag.put("branch", new Character('b'));
      prooflabel2tag.put("rule", new Character('r'));
      prooflabel2tag.put("term", new Character('t'));
      prooflabel2tag.put("formula", new Character('f'));
      prooflabel2tag.put("inst", new Character('i'));
      prooflabel2tag.put("ifseqformula", new Character('q'));
      prooflabel2tag.put("ifdirectformula", new Character('d'));
      prooflabel2tag.put("heur", new Character('h'));
      prooflabel2tag.put("builtin", new Character('n'));
      prooflabel2tag.put("keyLog", new Character('l'));
      prooflabel2tag.put("keyUser", new Character('u'));
      prooflabel2tag.put("keyVersion", new Character('v'));
      prooflabel2tag.put("keySettings", new Character('s'));
      prooflabel2tag.put("contract", new Character('c'));
      prooflabel2tag.put("ifInst", new Character('x'));		
      prooflabel2tag.put("userinteraction", new Character('a'));
      prooflabel2tag.put("newnames", new Character('w'));
      prooflabel2tag.put("autoModeTime", new Character('e'));
   }

   private NamespaceSet nss;
   private HashMap<String, String> category2Default = new LinkedHashMap<String, String>();
   private boolean onlyWith=false;
   private ImmutableSet<Choice> activatedChoices = DefaultImmutableSet.<Choice>nil();
   private HashSet usedChoiceCategories = new LinkedHashSet();
   private HashMap taclet2Builder;
   private AbbrevMap scm;
   private KeYExceptionHandler keh = null;
   
   
   private String filename;

   // these variables are set if a file is read in step by
   // step. This used when reading in LDTs because of cyclic
   // dependencies.
   private boolean skip_schemavariables;
   private boolean skip_functions;
   private boolean skip_transformers;
   private boolean skip_predicates;
   private boolean skip_sorts;
   private boolean skip_rulesets;
   private boolean skip_taclets;
   private boolean parse_includes = false;
   private Includes includes = new Includes();

   private boolean schemaMode = false;
   private ParserMode parserMode;

   private String chooseContract = null;
   private String proofObligation = null;
    
   private int savedGuessing = -1;

   private int lineOffset=0;
   private int colOffset=0;
   private int stringLiteralLine=0; // HACK!

   private Services services;
   private JavaReader javaReader;

   // if this is used then we can capture parts of the input for later use
   private DeclPicker capturer = null;
   private IProgramMethod pm = null;

   private LinkedHashMap<RuleKey, Taclet> taclets = new LinkedHashMap<RuleKey, Taclet>();
            
   private ImmutableSet<Contract> contracts = DefaultImmutableSet.<Contract>nil();
   private ImmutableSet<ClassInvariant> invs = DefaultImmutableSet.<ClassInvariant>nil();

   private ParserConfig schemaConfig;
   private ParserConfig normalConfig;
    
   // the current active config
   private ParserConfig parserConfig;

    private Term quantifiedArrayGuard = null;
    
    private String profileName;
    
    private TokenStream lexer;

    /**
     * Although the parser mode can be deduced from the particular constructor
     * used we still require the caller to provide the parser mode explicitly, 
     * so that the code is readable.
     */

   public KeYParser(ParserMode mode, TokenStream lexer, Services services) {
       this(mode, lexer);
       this.keh = services.getExceptionHandler();
   }

   /* Most general constructor, should only be used internally */
   private KeYParser(TokenStream lexer,
                     Services services,
		     NamespaceSet nss,
		     ParserMode mode) {
        this(lexer);
        this.lexer = lexer;
        this.parserMode = mode;
 	this.services = services;
	if(services != null)
          this.keh = services.getExceptionHandler();
	this.nss = nss;
    if (this.isTacletParser()) {
        switchToSchemaMode();
    } else {
        switchToNormalMode();
    }
   }

   /**
    * Used to construct Term parser - for first-order terms
    * and formulae.
    */
   public KeYParser(ParserMode mode,
                    TokenStream lexer,
                    JavaReader jr,
                    Services services,
                    NamespaceSet nss,
                    AbbrevMap scm) {
        this(lexer, services, nss, mode);
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
    public KeYParser(ParserMode mode, 
                     TokenStream lexer,
		     Services services,
		     NamespaceSet nss) {
        this(mode,
             lexer,
             new SchemaRecoder2KeY(services, nss),
             services,
             nss,
             new LinkedHashMap());
    }

    /**
     * Used to construct Taclet parser
     */  
    public KeYParser(ParserMode mode, 
                     TokenStream lexer,
                     SchemaJavaReader jr, 
                     Services services,  
                     NamespaceSet nss, 
                     HashMap taclet2Builder) {
        this(lexer, services, nss, mode);
        switchToSchemaMode();
        this.scm = new AbbrevMap();
        this.javaReader = jr;
        this.taclet2Builder = taclet2Builder;
    }


    /** 
     * Used to construct Problem parser
     */  
    public KeYParser(ParserMode mode, 
    		     TokenStream lexer, 
                     ParserConfig schemaConfig,
                     ParserConfig normalConfig, 
                     HashMap taclet2Builder,
                     ImmutableSet<Taclet> taclets) { 
        this(lexer, null, null, mode);
        if (lexer instanceof DeclPicker) {
            this.capturer = (DeclPicker) lexer;
        }
        if (normalConfig!=null)
        scm = new AbbrevMap();
        this.schemaConfig = schemaConfig;
        this.normalConfig = normalConfig;       
	switchToNormalMode();
        this.taclet2Builder = taclet2Builder;
        
        if (taclets != null && !taclets.isEmpty()) {
        	for (Taclet t : taclets) {
	  		this.taclets.put(new RuleKey(t), t);        	
        	}
        }
        
        if (normalConfig != null){
            this.keh = normalConfig.services().getExceptionHandler();
        } else{
            this.keh = new KeYRecoderExcHandler();
        }
    }

    public KeYParser(ParserMode mode, TokenStream lexer) {
        this(lexer, null, null, mode);
        if (lexer instanceof DeclPicker) {
            this.capturer = (DeclPicker) lexer;
        }
        scm = new AbbrevMap();
        this.schemaConfig = null;
        this.normalConfig = null;       
	switchToNormalMode();
        this.taclet2Builder = null;
        this.taclets = new LinkedHashMap<RuleKey, Taclet>();
        this.keh = new KeYRecoderExcHandler();
    }


    /**
     * Parses taclet from string.
     */
    public static Taclet parseTaclet(String s, Services services) {
   	try {
	    KeYParserF p =
                new KeYParserF(ParserMode.TACLET,
                              new KeYLexerF(s,
                                      "No file. KeYParser.parseTaclet(\n" + s + ")\n",
                                      null),
                              services,
                              services.getNamespaces());
	    return p.taclet(DefaultImmutableSet.<Choice>nil());
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    public void recover( RecognitionException ex, BitSet tokenSet ) /*throws TokenStreamException*/ {
     input.consume();
     int ttype = input.LA(1);
     while (ttype != Token.EOF && !tokenSet.member(ttype)) {
       input.consume();
       ttype = input.LA(1);
     }
    }
    
    public String getSourceName() {
    	if (super.getSourceName() == null) {
    		return filename;
    	}
    	return super.getSourceName();
    }

    public String getChooseContract() {
        return chooseContract;
    }
    
    public String getProofObligation() {
        return proofObligation;
    }
    
    public String getProfileName() {
      return profileName;
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

    public ImmutableSet<Choice> getActivatedChoices(){
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
    
     public TermFactory getTermFactory() {
       return getServices().getTermFactory();
    }

    public NamespaceSet namespaces() {
        if(isProblemParser()) 
          return parserConfig.namespaces();
        return nss;
    }

    private Namespace sorts() {
        return namespaces().sorts();
    }

    private Namespace functions() {
        return namespaces().functions();
    }

    private Namespace ruleSets() {
        return namespaces().ruleSets();
    }

    private Namespace variables() {
        return namespaces().variables();
    }

    private Namespace programVariables() {
        return namespaces().programVariables();
    }

    private Namespace choices(){
        return namespaces().choices();
    }

    public ImmutableSet<Taclet> getTaclets(){
	ImmutableSet<Taclet> tacletSet = DefaultImmutableSet.<Taclet>nil(); 
	
	/** maintain correct order for taclet lemma proofs */
	final List<Taclet> l = new LinkedList<Taclet>();	
	for (Taclet t : taclets.values()) {
		l.add(0,t);
	}
	
	
	for (Taclet t : l) {
		tacletSet = tacletSet.add(t);
	}
        return tacletSet;
    }

    public ImmutableSet<Contract> getContracts(){
        return contracts;
    }
    
    public ImmutableSet<ClassInvariant> getInvariants(){
    	return invs;
    }
    
    public HashMap<String, String> getCategory2Default(){
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
        return state.tokenStartLine;
    }   

    private int getColumn() {
        return state.tokenStartCharPositionInLine;
    }   

    private void resetSkips() {
       skip_schemavariables = false;
       skip_functions       = false;
       skip_transformers    = false;
       skip_predicates      = false;
       skip_sorts           = false;
       skip_rulesets        = false;
       skip_taclets         = false;
    }

    private void skipFuncs() {
        skip_functions = true;
    }

    private void skipTransformers() {
        skip_transformers = true;
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
            schemaConfig.namespaces().programVariables(),
            normalConfig.namespaces().variables(), 
            schemaConfig.namespaces().variables(), 
            normalConfig.namespaces().functions(), 
            schemaConfig.namespaces().functions(), 
          };
          return doLookup(n,lookups);
       } else {
          final Namespace[] lookups = {
              programVariables(), variables(),
              functions()
          };
          return doLookup(n,lookups);
       }
    }

    private Named doLookup(Name n, Namespace[] lookups) {
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
            int end = getSourceName().lastIndexOf(File.separator);
            int start = 0;
            filename = filename.replace('/', File.separatorChar);
            filename = filename.replace('\\', File.separatorChar);
            if(getSourceName().startsWith("file:")){
                start = 5;
            }
            File path=new File(getSourceName().substring(start,end+1)+filename);
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

    
    public void parseSorts() throws RecognitionException/*,
    				    TokenStreamException*/ {
      resetSkips();
      skipFuncs();
      skipTransformers();
      skipPreds();
      skipRuleSets();
      skipVars();
      skipTaclets();
      decls();
      resetSkips();
    }

    public void parseFunctions() throws RecognitionException/*, 
    					TokenStreamException*/ {
      resetSkips();
      skipSorts();
      skipTransformers();
      skipPreds();      
      skipRuleSets();
      skipVars();
      skipTaclets(); 
      decls();
      resetSkips();
    }

    public void parsePredicates() throws RecognitionException/*, 
    					 TokenStreamException*/ {
      resetSkips();
      skipSorts();
      skipFuncs();
      skipTransformers();
      skipRuleSets();
      skipVars();
      skipTaclets();
      decls();
      resetSkips();
    }

    public void parseFuncAndPred() throws RecognitionException/*, 
    					  TokenStreamException*/ {
      resetSkips();
      skipSorts();
      skipTransformers();
      skipRuleSets();
      skipVars();
      skipTaclets();
      decls();
      resetSkips();
    }
    
    public void parseRuleSets() throws RecognitionException/*, 
    				       TokenStreamException*/ {
      resetSkips();
      skipSorts();      
      skipFuncs();
      skipTransformers();
      skipPreds();
      skipVars();
      skipTaclets();
      decls();
      resetSkips();
    }
    
    public void parseVariables() throws RecognitionException/*, 
                                        TokenStreamException*/ {
      resetSkips();
      skipSorts();
      skipFuncs();
      skipTransformers();
      skipPreds();
      skipRuleSets();      
      skipTaclets();
      decls();
      resetSkips();
    }  

    public Term parseProblem() throws RecognitionException/*, 
    				      TokenStreamException*/ {
      resetSkips();
      skipSorts(); 
      skipFuncs();
      skipTransformers();
      skipPreds();
      skipRuleSets();
      //skipVars(); 
      skipTaclets();
      return problem();
    }

    public void parseIncludes() throws RecognitionException/*, 
    				        TokenStreamException*/ {
      parse_includes=true;
      problem();
    }

    public void parseWith() throws RecognitionException/*, 
    				   TokenStreamException*/ {
      onlyWith=true;
      problem();
    }

    private void schema_var_decl(String name, 
    				 Sort s, 
    				 boolean makeVariableSV,
            			 boolean makeSkolemTermSV,
            			 boolean makeTermLabelSV,
            			 SchemaVariableModifierSet mods) 
            			 	throws AmbigiousDeclException {
        if (!skip_schemavariables) {
            SchemaVariable v;
            if(s == Sort.FORMULA && !makeSkolemTermSV) {
                v = SchemaVariableFactory.createFormulaSV(new Name(name), 
                					  mods.rigid());
            } else if(s == Sort.UPDATE) {
                v = SchemaVariableFactory.createUpdateSV(new Name(name));
            } else if(s instanceof ProgramSVSort) {
                v = SchemaVariableFactory.createProgramSV(
                		new ProgramElementName(name),
                		(ProgramSVSort) s,
                		mods.list());
            } else {
                if(makeVariableSV) {
                    v = SchemaVariableFactory.createVariableSV
                    (new Name(name), s);
                } else if(makeSkolemTermSV) {
                    v = SchemaVariableFactory.createSkolemTermSV(new Name(name), 
                    				                 s);
                } else if (makeTermLabelSV) {
                	 v = SchemaVariableFactory.createTermLabelSV(new Name(name));
                } else { v = SchemaVariableFactory.createTermSV(
                					new Name(name), 
                					s, 
                					mods.rigid(), 
                					mods.strict());
                }
            }          

            if (inSchemaMode()) {
               if (variables().lookup(v.name()) != null) {
            	 throw new AmbigiousDeclException(v.name().toString(), 
            	 			          getSourceName(), 
            	  				  getLine(), 
            	  				  getColumn());
               }
               variables().add(v);
            }
        }
    }

    private Term toZNotation(String number, Namespace functions){    
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
        Term result = getTermFactory().createTerm((Function)functions.lookup(new Name("#")));

        for(int i = 0; i<s.length(); i++){
            result = getTermFactory().createTerm((Function)functions.lookup(new Name(s.substring(i,i+1))), result);
        }

       	if (negative) {
  	    result = getTermFactory().createTerm((Function) functions.lookup(new Name("neglit")), result);
        }
	return getTermFactory().createTerm
            ((Function) functions.lookup(new Name("Z")), result); 
    }

    private String getTypeList(ImmutableList<ProgramVariable> vars) {
	StringBuffer result = new StringBuffer("");
	final Iterator<ProgramVariable> it = vars.iterator();
	while (it.hasNext()) {
         result.append(it.next().getContainerType().getFullName());
         if (it.hasNext()) result.append(", ");         
	}
	return result.toString();
    }

    private Operator getAttribute(Sort prefixSort, String attributeName) 
           throws RecognitionException/*SemanticException*/ {
        final JavaInfo javaInfo = getJavaInfo();

        Operator result = null;
        
        if (inSchemaMode()) {
            // if we are currently reading taclets we look for schema variables first
            result = (SchemaVariable)variables().lookup(new Name(attributeName));
        }
        
        assert inSchemaMode() || result == null; 
        if (result == null) {
            
            final boolean unambigousAttributeName = attributeName.indexOf(':') != -1;

            if (unambigousAttributeName) {     
                result = javaInfo.getAttribute(attributeName);
            } else if(inSchemaMode() && attributeName.equals("length")) {
                try {
                    result = javaInfo.getArrayLength();
                } catch(Exception ex) {
                    keh.reportException
                       (new KeYSemanticException(input, getSourceName(), ex));
                }
            } else if(attributeName.equals("<inv>")) {
                // The invariant observer "<inv>" is implicit and 
                // not part of the class declaration
                // A special case is needed, hence.
                result = javaInfo.getInvProgramVar();
            } else {
                if (inSchemaMode()) {
                    semanticError("Either undeclared schema variable '" + 
                                  attributeName + "' or a not fully qualified attribute in taclet.");
                }
                final KeYJavaType prefixKJT = javaInfo.getKeYJavaType(prefixSort);
                if (prefixKJT == null) {
                    semanticError("Could not find type '"+prefixSort+"'. Maybe mispelled or "+
                        "you use an array or object type in a .key-file with missing " + 
                        "\\javaSource section.");
                }
                // WATCHOUT why not in DECLARATION MODE	   
                if(!isDeclParser()) {			      	
                    final ImmutableList<ProgramVariable> vars = 	
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
        }

        if ( result == null && !("length".equals(attributeName)) ) {
            throw new NotDeclException ("Attribute ", attributeName,
                getSourceName(), getLine(), getColumn());
        }
        return result;
    }

   
    public Term createAttributeTerm(Term prefix, 
    				    Operator attribute) throws RecognitionException/*SemanticException*/ {
        Term result = prefix;

        if (attribute instanceof SchemaVariable) {
            if (!inSchemaMode()) {
                semanticError("Schemavariables may only occur inside taclets.");
            }
	    SchemaVariable sv = (SchemaVariable) attribute;            
            if(sv.sort() instanceof ProgramSVSort 
                || sv.sort() == AbstractTermTransformer.METASORT) {
                semanticError("Cannot use schema variable " + sv + " as an attribute"); 
            }
            result = getServices().getTermBuilder().select(sv.sort(), 
                                           getServices().getTermBuilder().getBaseHeap(), 
                                           prefix, 
                                           getTermFactory().createTerm(attribute));
        } else {
            ProgramVariable pv = (ProgramVariable) attribute;
            if(pv instanceof ProgramConstant) {
                result = getTermFactory().createTerm(pv);
            } else if(pv == getServices().getJavaInfo().getArrayLength()) {
                result = getServices().getTermBuilder().dotLength(result);
            } else {
            	Function fieldSymbol 
            		= getServices().getTypeConverter()
            		               .getHeapLDT()
            		               .getFieldSymbolForPV((LocationVariable)pv, 
            		                                    getServices());        
            	if (pv.isStatic()){
                    result = getServices().getTermBuilder().staticDot(pv.sort(), fieldSymbol);
            	} else {            
                    result = getServices().getTermBuilder().dot(pv.sort(), result, fieldSymbol);                
            	}
            }
        }
        return result;
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
    throws RecognitionException/*KeYSemanticException*/ {
        KeYJavaType kjt = null;              
        try {
	    kjt=getJavaInfo().getTypeByClassName(s, null);
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
    
    private void unbindVars(Namespace orig) {
        if(isGlobalDeclTermParser()) {
            Debug.fail("unbindVars was called in Global Declaration Term parser.");
        }
        namespaces().setVariables(orig);
    }


    private Set progVars(JavaBlock jb) {
	if(isGlobalDeclTermParser()) {
  	  ProgramVariableCollector pvc
	      = new ProgramVariableCollector(jb.program(), getServices());
          pvc.start();
          return pvc.result();
        }else 
  	  if(!isDeclParser()) {
            if ((isTermParser() || isProblemParser()) && jb.isEmpty()) {
              return new LinkedHashSet();
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
        throws RecognitionException/*SemanticException*/ {
        if ( v instanceof LogicVariable || v instanceof ProgramVariable) {
            return getTermFactory().createTerm(v);
        } else {
	  if(isGlobalDeclTermParser())
		semanticError(v + " is not a logic variable");          
  	  if(isTermParser())
               semanticError(v + " is an unknown kind of variable.");
	  if (inSchemaMode() && v instanceof SchemaVariable ) {
               return getTermFactory().createTerm(v);
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
	return null;
    }
    
    private PairOfStringAndJavaBlock getJavaBlock(Token t) throws RecognitionException/*SemanticException*/ {
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
            throw new RecognitionException(input);
            //throw new JavaParserException(e.getMessage(), t.getText(), 
            //    getSourceName(), t.getLine(), t.getCharPositionInLine(), lineOffset, colOffset);
        } catch (de.uka.ilkd.key.java.ConvertException e) { 
            if (e.parseException()!=null
            &&  e.parseException().currentToken != null
            &&  e.parseException().currentToken.next != null) {               
                lineOffset=e.parseException().currentToken.next.beginLine;               
                colOffset=e.parseException().currentToken.next.beginColumn;
                e.parseException().currentToken.next.beginLine=getLine()-1;
                e.parseException().currentToken.next.beginColumn=getColumn();
                throw new RecognitionException(input);
                //throw new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine(), -1, -1);  // row/columns already in text
            }       
            if (e.proofJavaException()!=null
            &&  e.proofJavaException().currentToken != null
            &&  e.proofJavaException().currentToken.next != null) {      
                lineOffset = e.proofJavaException().currentToken.next.beginLine-1;
                colOffset=e.proofJavaException().currentToken.next.beginColumn;
                e.proofJavaException().currentToken.next.beginLine=getLine();
                e.proofJavaException().currentToken.next.beginColumn =getColumn();
                 throw new RecognitionException(input);
                 //throw  new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine(), lineOffset, colOffset); 
                            
            }   
            throw new RecognitionException(input);
            //throw new JavaParserException(e.getMessage(), t.getText(), getSourceName(), t.getLine(), t.getCharPositionInLine());
        } 
        return sjb;
    }

    /**
     * looks up and returns the sort of the given name or null if none has been found.
     * If the sort is not found for the first time, the name is expanded with "java.lang." 
     * and the look up restarts
     */
     private Sort lookupSort(String name) throws RecognitionException/*SemanticException*/ {
	Sort result = (Sort) sorts().lookup(new Name(name));
	if (result == null) {
	    if(name.equals(NullSort.NAME.toString())) {
	        Sort objectSort 
	        	= (Sort) sorts().lookup(new Name("java.lang.Object"));
	        if(objectSort == null) {
	            semanticError("Null sort cannot be used before "
	                          + "java.lang.Object is declared");
	        }
	        result = new NullSort(objectSort);
	        sorts().add(result);
	    } else {
  	    	result = (Sort) sorts().lookup(new Name("java.lang."+name));
  	    }
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
        throws RecognitionException/*NotDeclException, SemanticException*/ {

        // case 1: variable
        Operator v = (Operator) variables().lookup(new Name(varfunc_name));
        if (v != null && (args == null || (inSchemaMode() && v instanceof ModalOperatorSV))) {
            return v;
        }

        // case 2: program variable
        v = (Operator) programVariables().lookup
            (new ProgramElementName(varfunc_name));
        if (v != null && args==null) {
            return v;
        }
        
        // case 3: function
        v = (Operator) functions().lookup(new Name(varfunc_name));
        if (v != null) { // we allow both args==null (e.g. `c')
                         // and args.length=0 (e.g. 'c())' here 
            return v;
        }

        
        // case 4: instantiation of sort depending function
        int separatorIndex = varfunc_name.indexOf("::"); 
        if (separatorIndex > 0) {
            String sortName = varfunc_name.substring(0, separatorIndex);
            String baseName = varfunc_name.substring(separatorIndex + 2);
            Sort sort = lookupSort(sortName);
            SortDependingFunction firstInstance 
            	= SortDependingFunction.getFirstInstance(new Name(baseName), 
            					         getServices());
                        
            if(sort != null && firstInstance != null) {
                v = firstInstance.getInstanceFor(sort, getServices());
                if(v != null) {
                    return v;
                }
            } 
        }
        
        // not found
        if (args==null) {
            throw new NotDeclException
                ("(program) variable or constant", varfunc_name,
                 getSourceName(), getLine(), getColumn());
        } else {
            throw new NotDeclException
                ("function or static query", varfunc_name,
                 getSourceName(), getLine(), getColumn());
        }
    }

    private boolean isStaticAttribute() throws RecognitionException/*KeYSemanticException*/ {	
        if(inSchemaMode()) return false;
        final JavaInfo javaInfo = getJavaInfo();
        KeYJavaType kjt = null;
	boolean result = false;
//        try {
            int n = 1; 
            StringBuffer className = new StringBuffer(input.LT(n).getText());
	    while (isPackage(className.toString()) || input.LA(n+2)==NUM_LITERAL || 
	    		(input.LT(n+2)!=null && input.LT(n+2).getText()!=null && 
	    		input.LT(n+2).getText().length() > 0 && input.LT(n+2).getText().charAt(0)<='Z' && input.LT(n+2).getText().charAt(0)>='A' && 
	    		(input.LT(n+2).getText().length()==1 || 
	    		 input.LT(n+2).getText().charAt(1)<='z' && input.LT(n+2).getText().charAt(1)>='a'))){  	   
                if (input.LA(n+1) != DOT && input.LA(n+1) != EMPTYBRACKETS) return false;
                // maybe still an attribute starting with an uppercase letter followed by a lowercase letter
                if(getTypeByClassName(className.toString()) != null){
                    ProgramVariable maybeAttr = 
                    javaInfo.getAttribute(input.LT(n+2).getText(), getTypeByClassName(className.toString()));
                    if(maybeAttr!=null){
                        return true;
                    }
                }
                className.append(".");	       
                className.append(input.LT(n+2).getText());
                n+=2;
	    }	
        while (input.LA(n+1) == EMPTYBRACKETS) {
                className.append("[]");
                n++;
        }
	kjt = getTypeByClassName(className.toString());

	    if (kjt != null) { 
		// works as we do not have inner classes
		if (input.LA(n+1) == DOT) {
		    final ProgramVariable pv = 
		      javaInfo.getAttribute(input.LT(n+2).getText(), kjt);
		    result = (pv != null && pv.isStatic());		
		}    
	    }else{
	     result = false;
	    }
//	} catch (antlr.TokenStreamException tse) {
//	    // System.out.println("an exception occured"+tse);
//	    result = false;
//	}
	if(result && state.backtracking > 0) {
           savedGuessing = state.backtracking;
	   state.backtracking = 0;
	}
	return result;
    }

    private boolean isTermTransformer() /*throws TokenStreamException*/ {  
    if((input.LA(1) == IDENT &&
         AbstractTermTransformer.name2metaop(input.LT(1).getText())!=null)
       || input.LA(1) == IN_TYPE)
      return true;
    return false;
    }

    private boolean isStaticQuery() throws RecognitionException/*KeYSemanticException*/ {   
    if(inSchemaMode()) return false;
    final JavaInfo javaInfo = getJavaInfo();
    boolean result = false;
//    try {
        int n = 1; 
        KeYJavaType kjt = null;
        StringBuffer className = new StringBuffer(input.LT(n).getText());
        while (isPackage(className.toString())) {          
          if (input.LA(n+1) != DOT) return false;
          className.append(".");         
          className.append(input.LT(n+2).getText());
          n+=2;
        }   
        kjt = getTypeByClassName(className.toString());
        if (kjt != null) { 
           if (input.LA(n+1) == DOT && input.LA(n+3) == LPAREN) {
               Iterator<IProgramMethod> it = javaInfo.getAllProgramMethods(kjt).iterator();
               while(it.hasNext()) {
                 final IProgramMethod pm = it.next();
                 final String name = kjt.getFullName()+"::"+input.LT(n+2).getText();                 
                 if(pm != null && pm.isStatic() && pm.name().toString().equals(name) ) {
                   result = true;
		   break;
		 }
               }
           }   
        }
//    } catch (antlr.TokenStreamException tse) {
//        result = false;
//    }
    if(result && state.backtracking > 0) {
      savedGuessing = state.backtracking;
      state.backtracking = 0;
    }
    return result;
    }


    private TacletBuilder createTacletBuilderFor
        (Object find, int applicationRestriction) 
        throws RecognitionException/*InvalidFindException*/ {
        if ( applicationRestriction != RewriteTaclet.NONE &&
             applicationRestriction != RewriteTaclet.IN_SEQUENT_STATE &&
             !( find instanceof Term ) ) {
            String mod = "";
            if ((applicationRestriction & RewriteTaclet.SAME_UPDATE_LEVEL) != 0) {
                mod = "\"\\sameUpdateLevel\"";
            }
            if ((applicationRestriction & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\antecedentPolarity\""; 
            }
            if ((applicationRestriction & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
                if (mod != "") mod += " and ";
                mod += "\"\\succedentPolarity\"";
            }
            if (mod == "") {
                mod = "Application restrictions";               
            }
            
            throw new InvalidFindException
                ( mod +  " may only be used for rewrite taclets:" + find,
                 getSourceName(), getLine(), getColumn());
        }
        if ( find == null ) {
            return new NoFindTacletBuilder();
        } else if ( find instanceof Term ) {
            return new RewriteTacletBuilder().setFind((Term)find)
                .setApplicationRestriction(applicationRestriction);
        } else if ( find instanceof Sequent ) {
            Sequent findSeq = (Sequent) find;
            if ( findSeq.isEmpty() ) {
                return new NoFindTacletBuilder();
            } else if (   findSeq.antecedent().size() == 1
                          && findSeq.succedent().size() == 0 ) {
                Term findFma = findSeq.antecedent().get(0).formula();
                AntecTacletBuilder b = new AntecTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else if (   findSeq.antecedent().size() == 0
                          && findSeq.succedent().size() == 1 ) {
                Term findFma = findSeq.succedent().get(0).formula();
                SuccTacletBuilder b = new SuccTacletBuilder();
                b.setFind(findFma);
                b.setIgnoreTopLevelUpdates((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) == 0);
                return b;
            } else {
                throw new InvalidFindException
                    ("Unknown find-sequent (perhaps null?):"+findSeq,
                     getSourceName(), getLine(), getColumn());
            }
        } else {
            throw new InvalidFindException
                    ("Unknown find class type: " + find.getClass().getName(),
                     getSourceName(), getLine(), getColumn());
        }
    }       

    private void addGoalTemplate(TacletBuilder b,
                                 String id,
                                 Object rwObj,
                                 Sequent addSeq,
                                 ImmutableList<Taclet> addRList,
                                 ImmutableSet<SchemaVariable> pvs,
                                 ImmutableSet<Choice> soc) 
        throws RecognitionException/*SemanticException*/
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
                    throw new RecognitionException(input);
                        //new UnfittingReplacewithException
                        //("Replacewith without find", getSourceName(),
                        // getLine(), getColumn());
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
                             getSourceName(), getLine(), getColumn());
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
                             getSourceName(), getLine(), getColumn());
                    }
                }
            }
            gt.setName(id); 
            b.addTacletGoalTemplate(gt);
            if(soc != null) b.addGoal2ChoicesMapping(gt,soc);
        }
     
    public void testLiteral(String l1, String l2)
    throws RecognitionException/*KeYSemanticException*/
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
    throws RecognitionException/*, antlr.TokenStreamException*/{
        resetSkips();
        skipSorts(); skipFuncs(); skipPreds();    
        return problem();
    }

    /**
     * returns the ProgramMethod parsed in the jml_specifications section.
     */
    public IProgramMethod getProgramMethod(){
        return pm;
    }


    public void addFunction(Function f) {
        functions().add(f);
    }

    
    private ImmutableSet<Modality> lookupOperatorSV(String opName, ImmutableSet<Modality> modalities) 
    		throws RecognitionException/*KeYSemanticException*/ {
	ModalOperatorSV osv = (ModalOperatorSV)variables().lookup(new Name(opName));
        if(osv == null) {
	    semanticError("Schema variable "+opName+" not defined.");
	}
        modalities = modalities.union(osv.getModalities());
        return modalities;
    } 
    
    private ImmutableSet<Modality> opSVHelper(String opName, 
                                     ImmutableSet<Modality> modalities) 
        	throws RecognitionException/*KeYSemanticException*/ {
        if(opName.charAt(0) == '#') {
            return lookupOperatorSV(opName, modalities);           
        } else {
	    switchToNormalMode();
       	    Modality m = Modality.getModality(opName);
	    switchToSchemaMode();
            if(m == null) {
                semanticError("Unrecognised operator: "+opName);
            }
            modalities = modalities.add(m);
       }
       return modalities;
    }

    private void semanticError(String message) throws RecognitionException {
      throw new KeYSemanticException(input, getSourceName(), message);
    }

    private static class PairOfStringAndJavaBlock {
      String opName;
      JavaBlock javaBlock;
    }

}

// WATCHOUT Don't remove this. Ever!!! 
// Although it's not called, it is necessary for antlr to produce the 
// right parser.
top : a=formula {	 
   Debug.fail("KeYParser: top() should not be called. Ever.");	 
}	 
;

decls : 
        (one_include_statement)* {
           if(parse_includes) return;
           activatedChoices = DefaultImmutableSet.<Choice>nil();  
	}
        (options_choice)? 
        (
            {!onlyWith}?=> option_decls
        |    
            {!onlyWith}?=> sort_decls
        |
            {!onlyWith}?=> prog_var_decls
        |
            {!onlyWith}?=> schema_var_decls
        |
            pred_decls
        |
            func_decls
        |
            transform_decls
        |
            {!onlyWith}?=> ruleset_decls
        ) *
    ;

one_include_statement
@init{
   boolean ldts = false;
}
:
    (INCLUDE | (INCLUDELDTS {ldts = true; }))
    one_include[ldts] (COMMA one_include[ldts])* SEMI
;

one_include [boolean ldt]
:
        (absfile=IDENT{ 
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

activated_choice @init{
    String name;
    Choice c;
}:
        cat=IDENT COLON choice_=IDENT
        {if(usedChoiceCategories.contains(cat.getText())){
            throw new IllegalArgumentException("You have already chosen a different option for "+cat.getText());
        }
        usedChoiceCategories.add(cat.getText());
        name = cat.getText()+":"+choice_.getText();
        c = (Choice) choices().lookup(new Name(name));
        if(c==null){
            throw new NotDeclException("Option", choice_.getText(),
                                       getSourceName(), choice_.getLine(), choice_.getCharPositionInLine());
        }else{
            activatedChoices=activatedChoices.add(c);
        }
        }
    ;

option_decls
:
        OPTIONSDECL LBRACE (choice SEMI)* RBRACE 
    ;

choice @init{
    String cat=null;
}:
        category=IDENT {cat=category.getText();} (COLON LBRACE choice_option[cat] (COMMA choice_option[cat])* RBRACE)? 
        {
            if(!category2Default.containsKey(cat)){
                choices().add(new Choice("On",cat));
                choices().add(new Choice("Off",cat)); 
                category2Default.put(cat, cat+":On");               
            }
        }
    ;

choice_option[String cat]@init{
    String name;
}:
        choice_=IDENT { name=cat+":"+choice_.getText();
        Choice c = (Choice) choices().lookup(new Name(name));
        if(c==null){
            c = new Choice(choice_.getText(),cat);
            choices().add(c);
        }
            if(!category2Default.containsKey(cat)){
                category2Default.put(cat, name);
            }
        }
    ;

/* TODO: Why is the result of one_sort_decl stored in the local variables?
 * It does not seem to be employed at all ?! (MU)
 */
sort_decls 
@init{
  ImmutableList<Sort> lsorts = ImmutableSLList.<Sort>nil();
  multipleSorts = ImmutableSLList.<Sort>nil();
}
: SORTS LBRACE 
       ( multipleSorts = one_sort_decl { lsorts = lsorts.prepend(multipleSorts); })* 
  RBRACE 
;

one_sort_decl returns [ImmutableList<Sort> createdSorts = ImmutableSLList.<Sort>nil()] 
@init{
    boolean isAbstractSort = false;
    boolean isGenericSort = false;
    boolean isProxySort = false;
    sortExt=new Sort [0];
    sortOneOf=new Sort [0];
    sortIds = ImmutableSLList.<String>nil(); 
} : 
        ( 
         GENERIC {isGenericSort=true;} sortIds = simple_ident_comma_list
            ( ONEOF sortOneOf = oneof_sorts )? 
            ( EXTENDS sortExt = extends_sorts )?
        | PROXY {isProxySort=true;} sortIds = simple_ident_comma_list
            ( EXTENDS sortExt = extends_sorts )?
        | (ABSTRACT {isAbstractSort = true;})?
          firstSort = simple_ident_dots { sortIds = sortIds.prepend(firstSort); }
          (
              (EXTENDS sortExt = extends_sorts ) 
            | ((COMMA) sortIds = simple_ident_comma_list { sortIds = sortIds.prepend(firstSort) ; } )
          )?
        ) SEMI {   
            if (!skip_sorts) {
                    Iterator<String> it = sortIds.iterator ();        
                    while ( it.hasNext () ) {
                        Name sort_name = new Name(it.next());   
                        // attention: no expand to java.lang here!       
                        if (sorts().lookup(sort_name) == null) {
                            Sort s;
			    if (isGenericSort) {
                                int i;
                                ImmutableSet<Sort>  ext   = DefaultImmutableSet.<Sort>nil();
                                ImmutableSet<Sort>  oneOf = DefaultImmutableSet.<Sort>nil();

                                for ( i = 0; i != sortExt.length; ++i )
                                ext = ext.add ( sortExt[i] );

                                for ( i = 0; i != sortOneOf.length; ++i )
                                oneOf = oneOf.add ( sortOneOf[i] );
                                
                                try {
                                    s = new GenericSort(sort_name, ext, oneOf);
                                } catch (GenericSupersortException e) {
                                    throw new GenericSortException ( "sort", "Illegal sort given",
                                        e.getIllegalSort(), getSourceName(), getLine(), getColumn());
                                }
                            } else if (new Name("any").equals(sort_name)) {
                                s = Sort.ANY;
                            } else  {
                                ImmutableSet<Sort>  ext = DefaultImmutableSet.<Sort>nil();

                                for ( int i = 0; i != sortExt.length; ++i ) {
                                    ext = ext.add ( sortExt[i] );
                                }

                                if(isProxySort) {
                                    s = new ProxySort(sort_name, ext);
                                } else {
                                s = new SortImpl(sort_name, ext, isAbstractSort);
                                }
                            }
                            assert s != null;
                            sorts().add ( s ); 

                            createdSorts = createdSorts.append(s);
                        }
                }
            }
        };


simple_ident_dots returns [ String ident = ""; ] 
:
  id = simple_ident { ident += id; }  
    (DOT 
 	(id = simple_ident | num=NUM_LITERAL {id=num.getText();}) 
 	{ident += "." + id;})* 
 ;

extends_sorts returns [Sort[\] extendsSorts = null] 
@init{
    List args = new LinkedList();
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

oneof_sorts returns [Sort[\] oneOfSorts = null] 
@init{
    List args = new LinkedList();
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
@init{ 
   boolean array = false;
}
:
    type = simple_ident_dots (EMPTYBRACKETS {type += "[]"; array=true;})* 
    {
        kjt = getJavaInfo().getKeYJavaType(type);
            
        //expand to "java.lang"            
        if (kjt == null) {
            try {
                String guess = "java.lang." + type;
       	        kjt = getJavaInfo().getKeYJavaType(guess);
       	    } catch(Exception e) {
       	        kjt = null;
       	    }
        }
     
        //arrays
        if(kjt == null && array) {
            try {
                JavaBlock jb = getJavaInfo().readJavaBlock("{" + type + " k;}");
                kjt = ((VariableDeclaration) 
                        ((StatementBlock) jb.program()).getChildAt(0)).
                            getTypeReference().getKeYJavaType();
            } catch (Exception e) {
                kjt = null;
            }          
        }
     
        //try as sort without Java type (neede e.g. for "Heap")
        if(kjt == null) {
	    Sort sort = lookupSort(type);
	    if(sort != null) {
                kjt = new KeYJavaType(null, sort);
            }
        }
     
        if(kjt == null) {
            semanticError("Unknown type: " + type);
        }
    }
;

prog_var_decls 
@init{
    String var_name;
}
    :
        { switchToNormalMode();}
        PROGRAMVARIABLES
        LBRACE 
        (
            kjt = keyjavatype
            var_names = simple_ident_comma_list
            {
	        Iterator<String> it = var_names.iterator();
		while(it.hasNext()){
		  var_name = it.next();
		  ProgramElementName pvName = new ProgramElementName(var_name);
		  Named name = lookup(pvName);
                  if (name != null ) {
		    // commented out as pv do not have unique name (at the moment)
		    //  throw new AmbigiousDeclException
     		    //  	(var_name, getSourceName(), getLine(), getColumn());
		    if(!(name instanceof ProgramVariable) || (name instanceof ProgramVariable && 
			    !((ProgramVariable)name).getKeYJavaType().equals(kjt))) { 
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
     id=STRING_LITERAL {
       lit = id.getText();
       lit = lit.substring(1,lit.length()-1);
       stringLiteralLine = id.getLine();
     }
     ;

simple_ident returns [String ident = null]
   :
     id=IDENT { ident = id.getText(); }
   ;

simple_ident_comma_list returns [ImmutableList<String> ids = ImmutableSLList.<String>nil()]
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
@init{
    boolean makeVariableSV  = false;
    boolean makeSkolemTermSV = false;
    boolean makeTermLabelSV  = false;
    SchemaVariableModifierSet mods = null;
} :   
   (MODALOPERATOR one_schema_modal_op_decl SEMI)
 |
  ( 
   (
    PROGRAM
    { mods = new SchemaVariableModifierSet.ProgramSV (); }
    ( schema_modifiers[mods] ) ?
    id = simple_ident ( LBRACKET nameString = simple_ident EQUALS parameter = simple_ident_dots RBRACKET )? {
       if(nameString != null && !"name".equals(nameString)) {
         semanticError("Unrecognized token '"+nameString+"', expected 'name'");
       }
       ProgramSVSort psv = ProgramSVSort.name2sort().get(new Name(id));
       s = (Sort) (parameter != null ? psv.createInstance(parameter) : psv);
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
  | TERMLABEL 
    { makeTermLabelSV = true; }
    { mods = new SchemaVariableModifierSet.TermLabelSV (); }
    ( schema_modifiers[mods] ) ?   
    ids = simple_ident_comma_list 
  | UPDATE
    { mods = new SchemaVariableModifierSet.FormulaSV (); }
    ( schema_modifiers[mods] ) ?
    {s = Sort.UPDATE;}
    ids = simple_ident_comma_list 
  | SKOLEMFORMULA
    { makeSkolemTermSV = true; } 
    { mods = new SchemaVariableModifierSet.FormulaSV (); }
    ( schema_modifiers[mods] ) ?    
    {s = Sort.FORMULA;}
    ids = simple_ident_comma_list  
  | (    TERM
         { mods = new SchemaVariableModifierSet.TermSV (); }
         ( schema_modifiers[mods] ) ?
      | (VARIABLES
         { makeVariableSV = true; }
         { mods = new SchemaVariableModifierSet.VariableSV (); }
         ( schema_modifiers[mods] ) ?)
      | (SKOLEMTERM 
         { makeSkolemTermSV = true; }
         { mods = new SchemaVariableModifierSet.SkolemTermSV (); }
         ( schema_modifiers[mods] ) ?)    	
    )
    s = any_sortId_check[true]
    ids = simple_ident_comma_list 
  ) SEMI
   { 
     Iterator<String> it = ids.iterator();
     while(it.hasNext())
       schema_var_decl(it.next(),
                       s,
                       makeVariableSV,
                       makeSkolemTermSV,
                       makeTermLabelSV, 
		       mods);
   }
 )

 ;

schema_modifiers[SchemaVariableModifierSet mods]
    :
        LBRACKET
        opts = simple_ident_comma_list         
        RBRACKET
        {
            final Iterator<String> it = opts.iterator ();
            while ( it.hasNext () ) {
                final String option = it.next();
                if (!mods.addModifier(option))
                    semanticError(option+ 
                    ": Illegal or unknown modifier in declaration of schema variable");
            }
        }
    ;

one_schema_modal_op_decl
@init{
    ImmutableSet<Modality> modalities = DefaultImmutableSet.<Modality>nil();
    sort = Sort.FORMULA;
} 
    :
        (LPAREN sort = any_sortId_check[true] {
           if (sort != Sort.FORMULA) { 
               semanticError("Modal operator SV must be a FORMULA, not " + sort);
           }            
         } RPAREN)? 
        LBRACE ids = simple_ident_comma_list RBRACE id = simple_ident
	{   if (skip_schemavariables) {	       
	       return;
	    }	        
            Iterator<String> it1 = ids.iterator();
            while(it1.hasNext()) {
  	      modalities = opSVHelper(it1.next(), modalities);
  	    }
            SchemaVariable osv = (SchemaVariable)variables().lookup(new Name(id));
            if(osv != null)
              semanticError("Schema variable "+id+" already defined.");

            osv = SchemaVariableFactory.createModalOperatorSV(new Name(id),  
                        sort, modalities);
            
            if (inSchemaMode()) {
                variables().add(osv);
                //functions().add(osv);
            }
        }
    ;

pred_decl
    :
        pred_name = funcpred_name
        
        (
	    whereToBind = where_to_bind
	)?        
        
        
        argSorts = arg_sorts[!skip_predicates]
        {
            if (!skip_predicates) {
            
                if(whereToBind != null 
	 	   && whereToBind.length != argSorts.length) {
                    semanticError("Where-to-bind list must have same length "
                                  + "as argument list");
                }
                 
                Function p = null;            
            
            	int separatorIndex = pred_name.indexOf("::"); 
	        if (separatorIndex > 0) {
	            String sortName = pred_name.substring(0, separatorIndex);
	            String baseName = pred_name.substring(separatorIndex + 2);
		    Sort genSort = lookupSort(sortName);
		    
		    if(genSort instanceof GenericSort) {	        	            	
		    	p = SortDependingFunction.createFirstInstance(
		    	    		(GenericSort)genSort,
		    	    		new Name(baseName),
		    	    		Sort.FORMULA,
		    	    		argSorts,
		    	    		false);
		    }
	        }
            
                if(p == null) {	                        
                    p = new Function(new Name(pred_name), 
                    		     Sort.FORMULA, 
                    		     argSorts,
                    		     whereToBind,
                    		     false);
                }
		if (lookup(p.name()) != null) {
		    if(!isProblemParser()) {
		        throw new AmbigiousDeclException(p.name().toString(), 
		                                         getSourceName(), 
		                                         getLine(), 
		                                         getColumn());
		                                     
		    }
		}else{
                  addFunction(p);         
                }
            } 
        }
        SEMI
    ;

pred_decls 
    :
        PREDICATES 
        LBRACE
        (
            pred_decl
        ) *
        RBRACE
    ;


location_ident returns [int kind = NORMAL_NONRIGID]
    :
        id = simple_ident
       { 
          if ("Location".equals(id)) {
             kind = LOCATION_MODIFIER;
          } else if (!"Location".equals(id)) {
            semanticError(
                id+": Attribute of a Non Rigid Function can only be 'Location'");        
          }
       }
    ;



func_decl
@init{
    boolean unique = false;
}
    :
        (
            UNIQUE {unique=true;}
        )?
        
        retSort = any_sortId_check[!skip_functions]
        
        func_name = funcpred_name 
        
	(
	    whereToBind = where_to_bind
	)?        

        argSorts = arg_sorts[!skip_functions]
                
        {
            if (!skip_functions) {
            
	 	if(whereToBind != null 
	 	   && whereToBind.length != argSorts.length) {
                    semanticError("Where-to-bind list must have same length "
                                  + "as argument list");
                } 
            
                Function f = null;
                
	        int separatorIndex = func_name.indexOf("::"); 
	        if (separatorIndex > 0) {
	            String sortName = func_name.substring(0, separatorIndex);
	            String baseName = func_name.substring(separatorIndex + 2);
		    Sort genSort = lookupSort(sortName);
		    
		    if(genSort instanceof GenericSort) {	        	            	
		    	f = SortDependingFunction.createFirstInstance(
		    	    		(GenericSort)genSort,
		    	    		new Name(baseName),
		    	    		retSort,
		    	    		argSorts,
		    	    		unique);
		    }
	        }
	        
	        if(f == null) {
	            f = new Function(new Name(func_name), 
	                             retSort, 
	                             argSorts,
	                             whereToBind,
	                             unique);                    
	        }
		if (lookup(f.name()) != null) {
		    if(!isProblemParser()) {
		      throw new AmbigiousDeclException(f.name().toString(), 
		                                     getSourceName(), 
		                                     getLine(), 
		                                     getColumn());
		    }
		}else{
	    	    addFunction(f);
	        }
            } 
        }
        SEMI
    ;

func_decls
    :
        FUNCTIONS 
        LBRACE 
        (
            func_decl
        ) *
        RBRACE
    ;


// like arg_sorts but admits also the keyword "\formula"
arg_sorts_or_formula[boolean checkSort] returns [Sort[\] argSorts = null]
@init{
    List args = new LinkedList();
}
    :
        (
            LPAREN

            ( s = sortId_check[checkSort] { args.add(s); }
            | FORMULA {args.add(Sort.FORMULA);} )

            (
                COMMA ( s = sortId_check[checkSort] {args.add(s);}
                      | FORMULA {args.add(Sort.FORMULA);} )
            ) *
            RPAREN
        ) ?
        {
            argSorts = (Sort[])args.toArray(AN_ARRAY_OF_SORTS);
        }
    ;


transform_decl
    :
        (
          retSort = any_sortId_check[!skip_transformers]
        | FORMULA { retSort = Sort.FORMULA; }
        )

        trans_name = funcpred_name

        argSorts = arg_sorts_or_formula[!skip_transformers]

        {
            if (!skip_transformers) {

                Transformer t =
                    new Transformer(new Name(trans_name),
                                    retSort,
                                    new ImmutableArray<Sort>(argSorts));

                if (lookup(t.name()) != null) {
                    if(!isProblemParser()) {
                      throw new AmbigiousDeclException(t.name().toString(),
                                                       getSourceName(),
                                                       getLine(),
                                                       getColumn());
                    }
                } else {
                    addFunction(t);
                }
            }
        }
        SEMI
    ;

transform_decls
    :
        TRANSFORMERS
        LBRACE
        (
            transform_decl
        ) *
        RBRACE
    ;

arrayopid returns [KeYJavaType _array_op_id = null]
@after{ _array_op_id = componentType; }
    :
        EMPTYBRACKETS
        LPAREN
        componentType = keyjavatype
        RPAREN
    ;

arg_sorts[boolean checkSort] returns [Sort[\] argSorts = null] 
@init{
    List args = new LinkedList();
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
    
where_to_bind returns [Boolean[\] result = null]
@init{
    List<Boolean> list = new ArrayList<Boolean>();
}   
    : 
        LBRACE
        (  
            TRUE {list.add(true);} | FALSE {list.add(false);}  
        )
        (  
           COMMA
           (
               TRUE {list.add(true);} | FALSE {list.add(false);}
           )
        )*
        RBRACE    
        {
            result = list.toArray(new Boolean[0]);
        }
   ;

ruleset_decls
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

sortId returns [Sort _sort_id = null]
@after{ _sort_id = s; }
    :
        s = sortId_check[true]
    ;           

// Non-generic sorts, array sorts allowed
sortId_check [boolean checkSort] returns [Sort _sort_id_check = null]                
@after{ _sort_id_check = s; }
    :
        p = sortId_check_help[checkSort]
        s = array_decls[p, checkSort]
    ;

// Generic and non-generic sorts, array sorts allowed
any_sortId_check [boolean checkSort] returns [Sort _any_sort_id_check = null]                
@after{ _any_sort_id_check = s; }
    :   
        p = any_sortId_check_help[checkSort]
        s = array_decls[p, checkSort]
    ;
    
    
// Non-generic sorts
sortId_check_help [boolean checkSort] returns [Pair<Sort,Type> _sort_id_check_help = null]
@after{ _sort_id_check_help = result; }
    :
        result = any_sortId_check_help[checkSort]
        {
            // don't allow generic sorts or collection sorts of
            // generic sorts at this point
            Sort s = result.first;
            while ( s instanceof ArraySort ) {
            	s = ((ArraySort)s).elementSort ();
            }

            if ( s instanceof GenericSort ) {
                throw new GenericSortException ( "sort",
                    "Non-generic sort expected", s,
                    getSourceName (), getLine (), getColumn () );
            }
        }
    ;
    

// Generic and non-generic sorts
any_sortId_check_help [boolean checkSort] returns [Pair<Sort,Type> result = null]
    :
        name = simple_sort_name 
        {
            //Special handling for byte, char, short, long:
            //these are *not* sorts, but they are nevertheless valid
            //prefixes for array sorts such as byte[], char[][][].
            //Thus, we consider them aliases for the "int" sort, and remember
            //the corresponding Java type for the case that an array sort 
            //is being declared.
            Type t = null;            
            if(name.equals(PrimitiveType.JAVA_BYTE.getName())) {
                t = PrimitiveType.JAVA_BYTE;
                name = PrimitiveType.JAVA_INT.getName();
            } else if(name.equals(PrimitiveType.JAVA_CHAR.getName())) {
                t = PrimitiveType.JAVA_CHAR;
                name = PrimitiveType.JAVA_INT.getName();            
            } else if(name.equals(PrimitiveType.JAVA_SHORT.getName())) {
                t = PrimitiveType.JAVA_SHORT;
                name = PrimitiveType.JAVA_INT.getName();
            } else if(name.equals(PrimitiveType.JAVA_INT.getName())) {
                t = PrimitiveType.JAVA_INT;
                name = PrimitiveType.JAVA_INT.getName();
            } else if(name.equals(PrimitiveType.JAVA_LONG.getName())) {
                t = PrimitiveType.JAVA_LONG;
                name = PrimitiveType.JAVA_INT.getName();
            } else if(name.equals(PrimitiveType.JAVA_BIGINT.getName())){
                t = PrimitiveType.JAVA_BIGINT;
                name = PrimitiveType.JAVA_BIGINT.getName();
            }
            
            Sort s = null;
            if(checkSort) {
                s = lookupSort(name);
                if(s == null) {
                  throw new NotDeclException("sort", 
                                           name, 
                                           getSourceName(), 
                                           getLine(),  
                                           getColumn()); 
                }
            }
            
            result = new Pair<Sort,Type>(s, t);
        }
    ;


array_decls[Pair<Sort,Type> p, boolean checksort] returns [Sort s = null]                
@init{
    int n = 0;    
}
    :
     (EMPTYBRACKETS {n++;})*
        {   if (!checksort) return s;
            if(n != 0) {
                final JavaInfo ji = getJavaInfo();
                s = ArraySort.getArraySortForDim(p.first,
                				 p.second, 
                			         n, 
                			         ji.objectSort(),
                                                 ji.cloneableSort(), 
                                                 ji.serializableSort());

                Sort last = s;
                do {
                    final ArraySort as = (ArraySort) last;
                    sorts().add(as);                        
                    last = as.elementSort();
                } while (last instanceof ArraySort && sorts().lookup(last.name()) == null);
            } else {
                s = p.first;
            }
        }     
    ;
    

attrid returns [String attr = "";]
@init{
  classRef = "";
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
                     classRef, getSourceName(), getLine(), 
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
    :
        id=IDENT
        ( COLON s = sortId_check[true] ) ?
        {
            idd = new IdDeclaration ( id.getText (), s );
        }
    ;

funcpred_name returns [String result = null]
    :
     
    (sort_name DOUBLECOLON) => (prefix = sort_name 
        DOUBLECOLON name = simple_ident {result = prefix + "::" + name;})
  | 
    (prefix = simple_ident {result = prefix; })
;


// no array sorts
simple_sort_name returns [String name = ""]
    :
        id = simple_ident_dots  { name = id; } 
    ;


sort_name returns [String _sort_name = null]
@after{ _sort_name = name; }
    :
        name = simple_sort_name
        (brackets=EMPTYBRACKETS {name += brackets.getText();} )*
;

/**
 * In the special but important case of Taclets, we don't yet know
 * whether we are going to have a term or a formula, and it is hard
 * to decide a priori what we are looking at.  So the `term' 
 * non-terminal will recognize a term or a formula.  The `formula'
 * reads a formula/term and throws an error if it wasn't a formula.
 * This gives a rather late error message. */

formula returns [Term _formula = null] 
@after { _formula = a; }
    :
        a = term 
        {
            if (a != null && a.sort() != Sort.FORMULA ) {
                semanticError("Just Parsed a Term where a Formula was expected.");
            }
        }
    ;

term returns [Term _term = null]
@after { _term = result; }
    :
        result=elementary_update_term
        (
           PARALLEL a=elementary_update_term
           {
               result = getTermFactory().createTerm(UpdateJunctor.PARALLEL_UPDATE, result, a);
           }
            
        )*
    ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }
        
        
elementary_update_term returns[Term _elementary_update_term=null]
@after { _elementary_update_term = result; }
:
        result=equivalence_term 
        (
            ASSIGN a=equivalence_term
            {
                result = getServices().getTermBuilder().elementary(result, a);
            }
        )?
   ;
        catch [TermCreationException ex] {
              keh.reportException
			(new KeYSemanticException(input, getSourceName(), ex));
        }


equivalence_term returns [Term _equivalence_term = null] 
@after{ _equivalence_term = a; }
    :   a=implication_term 
        (EQV a1=implication_term 
            { a = getTermFactory().createTerm(Equality.EQV, new Term[]{a, a1});} )*
;
        catch [TermCreationException ex] {
              keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }

implication_term returns [Term _implication_term = null] 
@after{ _implication_term = a; }
    :   a=disjunction_term 
        (IMP a1=implication_term 
            { a = getTermFactory().createTerm(Junctor.IMP, new Term[]{a, a1});} )?
;
        catch [TermCreationException ex] {
              keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }

disjunction_term returns [Term _disjunction_term = null] 
@after { _disjunction_term = a; }
    :   a=conjunction_term 
        (OR a1=conjunction_term 
            { a = getTermFactory().createTerm(Junctor.OR, new Term[]{a, a1});} )*
;
        catch [TermCreationException ex] {
              keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }

conjunction_term returns [Term _conjunction_term = null] 
@after { _conjunction_term = a; }
    :   a=term60 
        (AND a1=term60
            { a = getTermFactory().createTerm(Junctor.AND, new Term[]{a, a1});} )*
            
;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

term60 returns [Term _term_60 = null] 
@after{ _term_60 = a; }
    :  
        a = unary_formula
    |   a = equality_term
;
        catch [TermCreationException ex] {
              keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }

unary_formula returns [Term _unary_formula = null] 
@after{ _unary_formula = a; }
    :  
        NOT a1  = term60 { a = getTermFactory().createTerm(Junctor.NOT,new Term[]{a1}); }
    |	a = quantifierterm 
    |   a = modality_dl_term
;
        catch [TermCreationException ex] {
              keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }


equality_term returns [Term _equality_term = null] 
@init{
    boolean negated = false;
}
@after { _equality_term = a; }
    :
        a =  logicTermReEntry // accessterm 
        // a term like {o:=u}x=y is parsed as {o:=u}(x=y)
        (  (EQUALS | NOT_EQUALS) =>
	      (EQUALS | NOT_EQUALS {negated = true;}) a1 = logicTermReEntry
            { 
                if (a.sort() == Sort.FORMULA ||
                    a1.sort() == Sort.FORMULA) {
                    String errorMessage = 
                    "The term equality \'=\'/\'!=\' is not "+
                    "allowed between formulas.\n Please use \'" + Equality.EQV +
                    "\' in combination with \'" + Junctor.NOT + "\' instead.";
                if (a.op() == Junctor.TRUE || a.op() == Junctor.FALSE ||
                    a1.op() == Junctor.TRUE || a1.op() == Junctor.FALSE) {
                    errorMessage += 
                    " It seems as if you have mixed up the boolean " +
                    "constants \'TRUE\'/\'FALSE\' " +
                    "with the formulas \'true\'/\'false\'.";
                }
                semanticError(errorMessage);
            }
            a = getTermFactory().createTerm(Equality.EQUALS, a, a1);

            if (negated) {
              a = getTermFactory().createTerm(Junctor.NOT, a);
            }
        })?
 ;
        catch [TermCreationException ex] {
              keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }

relation_op returns [Function op = null]
@init{
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
@init{
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
@init{
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
logicTermReEntry returns [Term _logic_term_re_entry = null]
@after { _logic_term_re_entry = a; }
:
   a = weak_arith_op_term ((relation_op) => op = relation_op a1=weak_arith_op_term {
                 a = getTermFactory().createTerm(op, a, a1);
              })?
;
        catch [TermCreationException ex] {
              keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }


weak_arith_op_term returns [Term _weak_arith_op_term = null]
@after { _weak_arith_op_term = a; }
:
   a = strong_arith_op_term ((weak_arith_op)=> op = weak_arith_op a1=strong_arith_op_term {
                  a = getTermFactory().createTerm(op, a, a1);
                })*
;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

strong_arith_op_term returns [Term _strong_arith_op_term = null]
@after { _strong_arith_op_term = a; }
:
   a = term110 ( (strong_arith_op) => op = strong_arith_op a1=term110 {
                  a = getTermFactory().createTerm(op, a, a1);
                })*
;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }


/**
 * helps to better distinguish if formulas are allowed or only term are
 * accepted
 * WATCHOUT: Woj: the check for Sort.FORMULA had to be removed to allow
 * infix operators and the whole bunch of grammar rules above.
 */
term110 returns [Term _term110 = null]
@after { _term110 = result; }
    :
        (
            result = accessterm  |
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
@init{}:
        
        id=IDENT {
            classReference = id.getText(); 
            while (isPackage(classReference)) {
                match(input, DOT, null);
                classReference += "." + input.LT(1).getText();
                match(input, IDENT, null);
            }      
            KeYJavaType kjt = null;
	    kjt = getTypeByClassName(classReference);
            if ( kjt == null) {
                throw new NotDeclException
                    ("Class " + classReference + " is unknown.", 
                     classReference, getSourceName(), getLine(), 
                     getColumn());
            }
	    classReference = kjt.getFullName();
        }  
    ;
*/




staticAttributeOrQueryReference returns [String attrReference = ""]
:
      //  attrReference=simple_ident_dots 
      id=IDENT
        {
            attrReference = id.getText(); 
            while (isPackage(attrReference) || input.LA(2)==NUM_LITERAL || 
                (input.LT(2).getText().charAt(0)<='Z' && input.LT(2).getText().charAt(0)>='A' && 
	    		(input.LT(2).getText().length()==1 || input.LT(2).getText().charAt(1)<='z' && input.LT(2).getText().charAt(1)>='a')) &&
                input.LA(1) == DOT) {
                if(getTypeByClassName(attrReference)!=null){
                    ProgramVariable maybeAttr = 
                    getJavaInfo().getAttribute(input.LT(2).getText(), getTypeByClassName(attrReference));
                    if(maybeAttr!=null){
                        break;
                    }
                }

                match(input, DOT, null);
                attrReference += "." + input.LT(1).getText();
                if(input.LA(1)==NUM_LITERAL){
                	match(input, NUM_LITERAL, null);
                }else{
               	 	match(input, IDENT, null);
                }
            }      
        }
        (EMPTYBRACKETS {attrReference += "[]";})*    
        {   KeYJavaType kjt = null;
            kjt = getTypeByClassName(attrReference);
            if (kjt == null) {
                throw new NotDeclException
                    ("Class " + attrReference + " is unknown.", 
                     attrReference, getSourceName(), getLine(), 
                     getColumn());
            }	        
            attrReference = kjt.getSort().name().toString();            
            match(input, DOT, null);
            attrReference += "::" + input.LT(1).getText();
            match(input, IDENT, null);
	    if(savedGuessing > -1) {
	      state.backtracking = savedGuessing;
	      savedGuessing = -1;
	    }
        }  
    ;

static_attribute_suffix returns [Term result = null]
@init{
    Operator v = null;
    attributeName = "";
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
        { result = createAttributeTerm(null, v); }                   
 ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }


attribute_or_query_suffix[Term prefix] returns [Term _attribute_or_query_suffix = null]
@init{
    Operator v = null;
    result = prefix;
    attributeName = "";    
}    
@after { _attribute_or_query_suffix = result; }
    :   
        DOT 
        ( 
           (IDENT (AT LPAREN simple_ident_dots RPAREN)? LPAREN)=>( result = query[prefix])
           | 
           attributeName = attrid 
           {   
              v = getAttribute(prefix.sort(), attributeName);
	      result = createAttributeTerm(prefix, v);
           }   
        )
 ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

query [Term prefix] returns [Term result = null] 
@init{
    classRef = "";
    boolean brackets = false;
}
    :
    mid=IDENT (AT LPAREN classRef = simple_ident_dots (EMPTYBRACKETS {brackets = true;} )? RPAREN)? args = argument_list
    { 
       if("".equals(classRef)){
          classRef = prefix.sort().name().toString();
       }else{
         if(brackets) classRef += "[]";
         KeYJavaType kjt = getTypeByClassName(classRef);
         if(kjt == null)
           throw new NotDeclException
             ("Class " + classRef + " is unknown.", 
              classRef, getSourceName(), getLine(), 
              getColumn());
         classRef = kjt.getFullName();
       }
       result = getServices().getJavaInfo().getProgramMethodTerm
                (prefix, mid.getText(), args, classRef);
    }        
 ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

static_query returns [Term result = null] 
@init{
    queryRef = "";
}
    :
    queryRef =  staticAttributeOrQueryReference args = argument_list
    { 
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
		 " but no corresponding java type!");
          }          
       }
	    
    }        
 ;
        catch [TermCreationException ex] {
        keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

//term120
accessterm returns [Term _accessterm = null] 
@after { _accessterm = result; }
    :
      (MINUS ~NUM_LITERAL) => MINUS result = term110
        {
            if (result.sort() != Sort.FORMULA) {
                result = getTermFactory().createTerm
                ((Function) functions().lookup(new Name("neg")), result);
            } else {
                semanticError("Formula cannot be prefixed with '-'");
            }
        } 
      |
      (LPAREN any_sortId_check[false] RPAREN term110)=> 
        LPAREN s = any_sortId_check[true] RPAREN result=term110 
        {
         final Sort objectSort = getServices().getJavaInfo().objectSort();
         if(s==null) {
           semanticError("Tried to cast to unknown type.");
         } else if (objectSort != null
                    && !s.extendsTrans(objectSort) 
                    && result.sort().extendsTrans(objectSort)) {
                semanticError("Illegal cast from " + result.sort() + 
                    " to sort " + s +
                    ". Casts between primitive and reference types are not allowed. ");
         }
         result = getTermFactory().createTerm(s.getCastSymbol(getServices()), result);
	}
      |
      ( {isStaticQuery()}? // look for package1.package2.Class.query(
        result = static_query
      |
        {isStaticAttribute()}?            // look for package1.package2.Class.attr
        result = static_attribute_suffix
      |
        result = atom
      )
         ( result = array_access_suffix[result]
         | result = attribute_or_query_suffix[result]
         | result = heap_update_suffix[result]
         )*
 ;
        catch [TermCreationException ex] {
               keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }

heap_update_suffix [Term heap] returns [Term _heap_update_suffix = null]
@init { result = heap; }
@after { _heap_update_suffix = result; }
    :
    LBRACE
    result=elementary_heap_update[result]
    ( PARALLEL result=elementary_heap_update[result] )*
    RBRACE
    ;

elementary_heap_update [Term heap] returns [Term result=heap]
    : // TODO find the right kind of super non-terminal for "o.f" and "a[i]"
      // and do not resign to parsing an arbitrary term
    ( (equivalence_term ASSIGN) => target=equivalence_term ASSIGN val=equivalence_term
        {
           Term objectTerm = target.sub(1);
           Term fieldTerm  = target.sub(2);
           result = getServices().getTermBuilder().store(heap, objectTerm, fieldTerm, val);
        }
    | id=simple_ident args=argument_list
        {
           Function f = (Function)functions().lookup(new Name(id));
           if(f == null) {
             semanticError("Unknown heap constructor " + id);
           }
           Term[] augmentedArgs = new Term[args.length+1];
           System.arraycopy(args, 0, augmentedArgs, 1, args.length);
           augmentedArgs[0] = heap;
           result = getTermFactory().createTerm(f, augmentedArgs);
           if(!result.sort().name().toString().equals("Heap")) {
              semanticError(id + " is not a heap constructor ");
           }
        }
    )
    ;
        catch [TermCreationException ex] {
               keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }

array_access_suffix [Term arrayReference] returns [Term _array_access_suffix = null] 
@init{
    Term rangeFrom = null;
    Term result = arrayReference;
}
@after{ _array_access_suffix = result; }
	:
  	LBRACKET 
	(   STAR {
           	rangeFrom = toZNotation("0", functions());
           	Term lt = getServices().getTermBuilder().dotLength(arrayReference);
           	Term one = toZNotation("1", functions());
  	   		rangeTo = getTermFactory().createTerm
           		((Function) functions().lookup(new Name("sub")), lt, one); 
        } 
        | indexTerm = logicTermReEntry 
	        ((DOTRANGE) => DOTRANGE rangeTo = logicTermReEntry
		                 {rangeFrom = indexTerm;})?
    )
    RBRACKET 
    {       
	if(rangeTo != null) {
		if(quantifiedArrayGuard == null) {
			semanticError(
  		  	"Quantified array expressions are only allowed in locations.");
		}
		LogicVariable indexVar = new LogicVariable(new Name("i"), 
		   	   		   (Sort) sorts().lookup(new Name("int")));
		indexTerm = getTermFactory().createTerm(indexVar);
		   	
		Function leq = (Function) functions().lookup(new Name("leq"));
		Term fromTerm = getTermFactory().createTerm(leq, rangeFrom, indexTerm);
		Term toTerm = getTermFactory().createTerm(leq, indexTerm, rangeTo);
		Term guardTerm = getTermFactory().createTerm(Junctor.AND, fromTerm, toTerm);
		quantifiedArrayGuard = getTermFactory().createTerm(Junctor.AND, quantifiedArrayGuard, guardTerm);
		}
            result = getServices().getTermBuilder().dotArr(result, indexTerm); 
    }            
    ;
        catch [TermCreationException ex] {
               keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
        }



accesstermlist returns [HashSet accessTerms = new LinkedHashSet()] :
     (t=accessterm {accessTerms.add(t);} ( COMMA t=accessterm {accessTerms.add(t);})* )? ;


atom returns [Term _atom = null]
@after { _atom = a; }
    :
(        {isTermTransformer()}? a = specialTerm
    |   a = funcpredvarterm
    |   LPAREN a = term RPAREN
    |   TRUE  { a = getTermFactory().createTerm(Junctor.TRUE); }
    |   FALSE { a = getTermFactory().createTerm(Junctor.FALSE); }
    |   a = ifThenElseTerm
    |   a = ifExThenElseTerm
    |   literal=STRING_LITERAL
        {
            a = getServices().getTypeConverter().convertToLogicElement(new de.uka.ilkd.key.java.expression.literal.StringLiteral(literal.getText()));
        }   
    ) (LGUILLEMETS labels = label {if (labels.size() > 0) {a = getServices().getTermBuilder().label(a, labels);} } RGUILLEMETS)?
    ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

label returns [ImmutableArray<TermLabel> labels = new ImmutableArray<TermLabel>()]
@init {
  ArrayList<TermLabel> labelList = new ArrayList<TermLabel>();
}
:
   l=single_label {labelList.add(l);} (COMMA l=single_label {labelList.add(l);})*
   {
	labels = new ImmutableArray<TermLabel>((TermLabel[])labelList.toArray(new TermLabel[labelList.size()]));
   }
;

single_label returns [TermLabel label=null]
@init {
  String labelName = "";
  TermLabel left = null;
  TermLabel right = null;
  List<String> parameters = new LinkedList<String>();
}
:
  (name=IDENT {labelName=name.getText();} | star=STAR {labelName=star.getText();} ) (LPAREN param1=STRING_LITERAL {parameters.add(param1.getText().substring(1,param1.getText().length()-1));} (COMMA param2=STRING_LITERAL {parameters.add(param2.getText().substring(1,param2.getText().length()-1));})* RPAREN)?
  {
      try {
          if (inSchemaMode()) {
               Named var = variables().lookup(new Name(labelName));
               if (var instanceof TermLabel) {
                    label = (TermLabel)var;
               }
          }
          if (label == null) {
                label = getServices().getProfile()
                                .getTermLabelManager().parseLabel(labelName, parameters);
          }
      } catch(TermLabelException ex) {
          keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
      }
  }
  ;


abbreviation returns [Term _abbreviation=null]
@init{ Term a = null; }
@after{ _abbreviation = a; }
    :
        (   sc = simple_ident
            {
                a =  scm.getTerm(sc);
                if(a==null){
                    throw new NotDeclException
                        ("abbreviation", sc, 
                         getSourceName(), getLine(), getColumn());
                }                                
            }
        )
    ;


ifThenElseTerm returns [Term _if_then_else_term = null]
@init{ Term result = null; }
@after{ _if_then_else_term = result; }
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
            result = getTermFactory().createTerm ( IfThenElse.IF_THEN_ELSE, new Term[]{condF, thenT, elseT} );
        }
 ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }
        
        
ifExThenElseTerm returns [Term _if_ex_then_else_term = null]
@init{
    exVars 
    	= ImmutableSLList.<QuantifiableVariable>nil();
    Namespace orig = variables();
    Term result = null;
}
@after{ _if_ex_then_else_term = result; }
    :
        IFEX exVars = bound_variables
        LPAREN condF = term RPAREN
        {
            if (condF.sort() != Sort.FORMULA) {
                semanticError
		  ("Condition of an \\ifEx-then-else term has to be a formula.");
            }
        }
        THEN LPAREN thenT = term RPAREN
        ELSE LPAREN elseT = term RPAREN
        {
            ImmutableArray<QuantifiableVariable> exVarsArray
            	= new ImmutableArray<QuantifiableVariable>( 
            	     exVars.toArray(new QuantifiableVariable[exVars.size()]));
            result = getTermFactory().createTerm ( IfExThenElse.IF_EX_THEN_ELSE,  
                                     new Term[]{condF, thenT, elseT}, 
                                     exVarsArray, 
                                     null );
            if(!isGlobalDeclTermParser()) {
                unbindVars(orig);
            }
        }
 ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }        


argument returns [Term _argument = null]
@init{
    ImmutableArray<QuantifiableVariable> vars = null;
}
@after{ _argument = result; }
:
 (
   // WATCHOUT Woj: can (should) this be unified to term60?
   {isTermParser() || isGlobalDeclTermParser()}? 
     result = term 
  |  
     result = term60 
 )
 ;
  

quantifierterm returns [Term _quantifier_term = null]
@init{
    Operator op = null;
    Namespace orig = variables();  
    Term a = null;
}
@after{ _quantifier_term = a; }
:
        (   FORALL { op = Quantifier.ALL; }
          | EXISTS  { op = Quantifier.EX;  })
        vs = bound_variables a1 = term60
        {
            a = getTermFactory().createTerm((Quantifier)op,
                              new ImmutableArray<Term>(a1),
	       		      new ImmutableArray<QuantifiableVariable>(vs.toArray(new QuantifiableVariable[vs.size()])),
	       		      null);
            if(!isGlobalDeclTermParser())
              unbindVars(orig);
        }
;

//term120_2
update_or_substitution returns [Term _update_or_substitution = null]
@after{ _update_or_substitution = result; }
:
      (LBRACE SUBST) => result = substitutionterm
      |  result = updateterm
    ; 

substitutionterm returns [Term _substitution_term = null] 
@init{
  SubstOp op = WarySubstOp.SUBST;
   Namespace orig = variables();  
  Term result = null;
}
@after{ _substitution_term = result; }
:
   LBRACE SUBST
     v = one_bound_variable SEMI
     { // Tricky part, v cannot be bound while parsing a1
       if(!isGlobalDeclTermParser())
          unbindVars(orig);
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
      result = getServices().getTermBuilder().subst ( op, v, a1, a2 );
      if(!isGlobalDeclTermParser())
        unbindVars(orig);
   }
;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }


updateterm returns [Term _update_term = null] 
@init{ Term result = null; }
@after{ _update_term = result; }
:
        LBRACE u=term RBRACE 
        ( 
            a2=term110 
            | 
            a2=unary_formula 
        )
        {   
	    result = getTermFactory().createTerm(UpdateApplication.UPDATE_APPLICATION, u, a2);
        }
   ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }           
        
bound_variables returns[ImmutableList<QuantifiableVariable> list = ImmutableSLList.<QuantifiableVariable>nil()]
:
      var = one_bound_variable { list = list.append(var); }
      (
          COMMA var = one_bound_variable { list = list.append(var); }
      )*
      SEMI
;

one_bound_variable returns[QuantifiableVariable _one_bound_variable=null]
@after{ _one_bound_variable = v; }
:
  {isGlobalDeclTermParser()}? v = one_logic_bound_variable_nosort
 |
  {inSchemaMode()}? v = one_schema_bound_variable
 |
  {!inSchemaMode()}? v = one_logic_bound_variable
;

one_schema_bound_variable returns[QuantifiableVariable v=null]
@init{
  Operator ts = null;
}
:
   id = simple_ident {
      ts = (Operator) variables().lookup(new Name(id));   
      if ( ! (ts instanceof VariableSV)) {
        semanticError(ts+" is not allowed in a quantifier. Note, that you can't "
        + "use the normal syntax for quantifiers of the form \"\\exists int i;\""
        + " in taclets. You have to define the variable as a schema variable"
        + " and use the syntax \"\\exists i;\" instead.");
      }
      v = (QuantifiableVariable) ts;
      bindVar();
   }
;

one_logic_bound_variable returns[QuantifiableVariable v=null]
:
  s=sortId id=simple_ident {
    v = bindVar(id, s);
  }
;

one_logic_bound_variable_nosort returns[QuantifiableVariable v=null]
:
  id=simple_ident {
    v = (LogicVariable)variables().lookup(new Name(id));
  }
;

modality_dl_term returns [Term _modality_dl_term = null]
@init{
    Operator op = null;
    PairOfStringAndJavaBlock sjb = null;
    Term a = null;
}
@after{ _modality_dl_term = a; }
   :
   modality = MODALITY
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
         op = Modality.getModality(sjb.opName);
       }
       if(op == null) {
         semanticError("Unknown modal operator: "+sjb.opName);
       }
     }
   // CAREFUL here, op can be null during guessing stage (use lazy &&)
   ({op != null && op.arity() == 1}? a1=term60
     // This here will accept both (1) \modality...\endmodality post and
     // (2) \modality...\endmodality(post)
     // so that it is consistent with pretty printer that prints (1).
     // A term "(post)" seems to be parsed as "post" anyway
      {
            a = getTermFactory().createTerm(op, new Term[]{a1}, null, sjb.javaBlock);
      }
   )
   ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }


argument_list returns [Term[\] _argument_list = null]
@init{
    List<Term> args = new LinkedList<Term>();
    Term[] result = null;
}
@after{ _argument_list = result; }
    :
        LPAREN 
        (p1 = argument { args.add(p1);  }

            (COMMA p2 = argument { args.add(p2); } )* )?

        RPAREN
        {
            result = args.toArray(new Term[0]);
        }

    ;

funcpredvarterm returns [Term _func_pred_var_term = null]
@init{
    String neg = "";
    boolean opSV = false;
    Namespace orig = variables();
    boolean limited = false;  
}
@after { _func_pred_var_term = a; }
    :
      ch=CHAR_LITERAL {
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
            a = getTermFactory().createTerm((Function) functions().lookup(new Name("C")), 
                                      toZNotation(""+intVal, functions()).sub(0));
        }
    | 
        ((MINUS)? NUM_LITERAL) => (MINUS {neg = "-";})? number=NUM_LITERAL
        { a = toZNotation(neg+number.getText(), functions());}    
    | AT a = abbreviation
    | varfuncid = funcpred_name (LIMITED {limited = true;})?
        ( (~LBRACE | LBRACE bound_variables) =>
            (
               LBRACE 
               boundVars = bound_variables 
               RBRACE 
            )?

            args = argument_list
        )? 
        
        //args==null indicates no argument list
        //args.size()==0 indicates open-close-parens ()
                
        {  
            if(varfuncid.equals("inReachableState") && args == null) {
	        a = getServices().getTermBuilder().wellFormed(getServices().getTypeConverter().getHeapLDT().getHeap());
	    } else if(varfuncid.equals("skip") && args == null) {
	        a = getTermFactory().createTerm(UpdateJunctor.SKIP);
	    } else {
	            Operator op = lookupVarfuncId(varfuncid, args);  
	            if(limited) {
	                if(op.getClass() == ObserverFunction.class) {
	                    op = getServices().getSpecificationRepository()
	                                      .limitObs((ObserverFunction)op).first;
	                } else {
	                    semanticError("Cannot can be limited: " + op);
	                }
	            }   
	                   
	            if (op instanceof ParsableVariable) {
	                a = termForParsedVariable((ParsableVariable)op);
	            } else {
	                if (args==null) {
	                    args = new Term[0];
	                }
	
	                if(boundVars == null) {
	                    a = getTermFactory().createTerm(op, args);
	                } else {
	                    //sanity check
	                    assert op instanceof Function;
	                    for(int i = 0; i < args.length; i++) {
	                        if(i < op.arity() && !op.bindVarsAt(i)) {
	                            for(QuantifiableVariable qv : args[i].freeVars()) {
	                                if(boundVars.contains(qv)) {
	                                    semanticError("Building function term "+op+" with bound variables failed: "
	                                                   + "Variable " + qv + " must not occur free in subterm " + args[i]);
	                                } 
	                            }	                            
	                        }
	                    }
	                    
	                    //create term
	                    a = getTermFactory().createTerm(op, args, new ImmutableArray<QuantifiableVariable>(boundVars.toArray(new QuantifiableVariable[boundVars.size()])), null);
	                }
	            }
	    }
	    
	    if(boundVars != null) {
	        unbindVars(orig);
	    }
        }
;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

specialTerm returns [Term _special_term = null] 
@init{
    Operator vf = null;
}
@after { _special_term = result; }:
     {isTacletParser() || isProblemParser()}?
       result = metaTerm
   ;
        catch [TermCreationException ex] {
              keh.reportException
		(new KeYSemanticException(input, getSourceName(), ex));
        }

arith_op returns [String op = null]
:
    PERCENT {op = "\%";}
  | STAR {op = "*";}
  | MINUS {op = "-";}
  | SLASH {op = "/";}
  | PLUS { op = "+";}
;


varId returns [ParsableVariable v = null]
    :
        id=IDENT 
        {   
            v = (ParsableVariable) variables().lookup(new Name(id.getText()));
            if (v == null) {
                throw new NotDeclException("variable", id.getText(), 
                                           getSourceName(), id.getLine(), id.getCharPositionInLine());
            }
        } 
  ;

varIds returns [LinkedList list = new LinkedList()]
@init{
   ParsableVariable v = null;
}
    :
      ids = simple_ident_comma_list {
         Iterator<String> it = ids.iterator();
	 while(it.hasNext()) {
	    String id = it.next();
            v = (ParsableVariable) variables().lookup(new Name(id));
            if (v == null) {
               semanticError("Variable " +id + " not declared.");
            }
	    list.add(v);
	 }
      }
  ;

triggers[TacletBuilder b]
@init {
   id = null;
   t = null;
   Named triggerVar = null;
   avoidCond = null;
   ImmutableList<Term> avoidConditions = ImmutableSLList.<Term>nil();
} :
   TRIGGER
     LBRACE id = simple_ident 
     	{  
     	  triggerVar = variables().lookup(new Name(id));
     	  if (triggerVar == null || !(triggerVar instanceof SchemaVariable)) {
     	  	semanticError("Undeclared schemavariable: " + id);
     	  }  
     	}   RBRACE     
     t=term (AVOID avoidCond=term {avoidConditions = avoidConditions.append(avoidCond);} 
      (COMMA avoidCond=term {avoidConditions = avoidConditions.append(avoidCond);})*)? SEMI
   {
     b.setTrigger(new Trigger((SchemaVariable)triggerVar, t, avoidConditions));
   }
;

taclet[ImmutableSet<Choice> choices] returns [Taclet r] 
@init{ 
    ifSeq = Sequent.EMPTY_SEQUENT;
    TacletBuilder b = null;
    int applicationRestriction = RewriteTaclet.NONE;
    choices_ = choices;
}
    : 
        name=IDENT (choices_=option_list[choices_])? 
        LBRACE {
	  //  schema var decls
	  namespaces().setVariables(new Namespace(variables()));
        } 
	( SCHEMAVAR one_schema_var_decl ) *
        ( ASSUMES LPAREN ifSeq=seq RPAREN ) ?
        ( FIND LPAREN find = termorseq RPAREN 
            (   SAMEUPDATELEVEL { applicationRestriction |= RewriteTaclet.SAME_UPDATE_LEVEL; }
              | INSEQUENTSTATE { applicationRestriction |= RewriteTaclet.IN_SEQUENT_STATE; }
              | ANTECEDENTPOLARITY { applicationRestriction |= RewriteTaclet.ANTECEDENT_POLARITY; }
              | SUCCEDENTPOLARITY { applicationRestriction |= RewriteTaclet.SUCCEDENT_POLARITY; }
            )*
        ) ?
        { 
            b = createTacletBuilderFor(find, applicationRestriction);
            b.setName(new Name(name.getText()));
            b.setIfSequent(ifSeq);
        }
        ( VARCOND LPAREN varexplist[b] RPAREN ) ?
        goalspecs[b, find != null]
        modifiers[b]
        RBRACE
        { 
            b.setChoices(choices_);
            r = b.getTaclet(); 
            taclet2Builder.put(r,b);
	  // dump local schema var decls
	  namespaces().setVariables(variables().parent());
        }
    ;

modifiers[TacletBuilder b]
: 
        ( rs = rulesets {
           Iterator it = rs.iterator();
           while(it.hasNext())
               b.addRuleSet((RuleSet)it.next());
         }
        | NONINTERACTIVE { b.addRuleSet((RuleSet)ruleSets().lookup(new Name("notHumanReadable"))); }
        | DISPLAYNAME dname = string_literal 
            {b.setDisplayName(dname);}
        | HELPTEXT htext = string_literal
            {b.setHelpText(htext);}
        | triggers[b]            
        ) *
    ;

seq returns [Sequent s] : 
        ant=semisequent SEQARROW suc=semisequent
        { s = Sequent.createSequent(ant, suc); }
    ;
     catch [RuntimeException ex] {
         keh.reportException
                (new KeYSemanticException(input, getSourceName(), ex));
     }
     
termorseq returns [Object o]
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
                                          new SequentFormula(head)).semisequent();
                    o = Sequent.createSequent(ant,ss);
                }
            } else {
                // A sequent.  Prepend head to the antecedent.
                Semisequent newAnt = s.antecedent();
                newAnt = newAnt .insertFirst(
                                             new SequentFormula(head)).semisequent();
                o = Sequent.createSequent(newAnt,s.succedent());
            }
        }
    |
        SEQARROW ss=semisequent
        {
            o = Sequent.createSequent(Semisequent.EMPTY_SEMISEQUENT,ss);
        }
    ;

semisequent returns [Semisequent _semi_sequent]
@init{ 
    ss = Semisequent.EMPTY_SEMISEQUENT; 
}
@after{ _semi_sequent = ss; }
    :
        /* empty */ | 
        head=term ( COMMA ss=semisequent) ? 
        { 
          ss = ss.insertFirst(new SequentFormula(head)).semisequent(); 
        }
    ;

varexplist[TacletBuilder b] : varexp[b] ( COMMA varexp[b] ) * ;

varexp[TacletBuilder b]
@init{
  boolean negated = false;
}
:
  ( varcond_applyUpdateOnRigid[b]
    | varcond_dropEffectlessElementaries[b]
    | varcond_dropEffectlessStores[b]
    | varcond_enum_const[b]
    | varcond_free[b]
    | varcond_hassort[b]
    | varcond_fieldtype[b]
    | varcond_equalUnique[b]
    | varcond_new[b]
    | varcond_newlabel[b]
    | varcond_observer[b]
    | varcond_different[b]
    | varcond_metadisjoint[b]
    | varcond_simplifyIfThenElseUpdate[b]
    | varcond_differentFields[b]
  ) 
  | 
  ( (NOT_ {negated = true;} )? 
    (   varcond_abstractOrInterface[b, negated]
	    | varcond_array[b, negated]
        | varcond_array_length[b, negated]	
        | varcond_enumtype[b, negated]
        | varcond_freeLabelIn[b,negated]         
        | varcond_localvariable[b, negated]        
        | varcond_thisreference[b, negated]        
        | varcond_reference[b, negated]        
        | varcond_referencearray[b, negated]
        | varcond_static[b,negated]
        | varcond_staticmethod[b,negated]  
        | varcond_typecheck[b, negated]
        | varcond_constant[b, negated]
        | varcond_label[b, negated]
        | varcond_static_field[b, negated]
        | varcond_subFormulas[b, negated]
      )
  )
;


varcond_applyUpdateOnRigid [TacletBuilder b]
:
   APPLY_UPDATE_ON_RIGID LPAREN u=varId COMMA x=varId COMMA x2=varId RPAREN 
   {
      b.addVariableCondition(new ApplyUpdateOnRigidCondition((UpdateSV)u, 
                                                             (SchemaVariable)x, 
                                                             (SchemaVariable)x2));
   }
;

varcond_dropEffectlessElementaries[TacletBuilder b]
:
   DROP_EFFECTLESS_ELEMENTARIES LPAREN u=varId COMMA x=varId COMMA result=varId RPAREN 
   {
      b.addVariableCondition(new DropEffectlessElementariesCondition((UpdateSV)u, 
                                                                     (SchemaVariable)x, 
                                                                     (SchemaVariable)result));
   }
;

varcond_dropEffectlessStores[TacletBuilder b]
:
   DROP_EFFECTLESS_STORES LPAREN h=varId COMMA o=varId COMMA f=varId COMMA x=varId COMMA result=varId RPAREN 
   {
      b.addVariableCondition(new DropEffectlessStoresCondition((TermSV)h,
      							       (TermSV)o,
      							       (TermSV)f,
      							       (TermSV)x, 
                                                               (TermSV)result));
   }
;

varcond_differentFields [TacletBuilder b]
:
   DIFFERENTFIELDS
   LPAREN
     x = varId COMMA y = varId
   RPAREN
   {
            b.addVariableCondition(new DifferentFields((SchemaVariable)x, (SchemaVariable)y));
   }
;


varcond_simplifyIfThenElseUpdate[TacletBuilder b]
:
   SIMPLIFY_IF_THEN_ELSE_UPDATE LPAREN phi=varId COMMA u1=varId COMMA u2=varId COMMA commonFormula=varId COMMA result=varId RPAREN 
   {
      b.addVariableCondition(new SimplifyIfThenElseUpdateCondition((FormulaSV) phi,
      															   (UpdateSV) u1,
      															   (UpdateSV) u2,
      															   (FormulaSV) commonFormula,
                                                                   (SchemaVariable)result));
   }
;

type_resolver returns [TypeResolver tr = null] 
:
    (s = any_sortId_check[true]      
        {
            if ( s instanceof GenericSort ) {
                tr = TypeResolver.createGenericSortResolver((GenericSort)s);
            } else {
                tr = TypeResolver.createNonGenericSortResolver(s);
            }
        }
    ) 
    |
    ( 
        TYPEOF LPAREN y = varId RPAREN  
        {  
            tr = TypeResolver.createElementTypeResolver((SchemaVariable)y); 
        } 
    )
    |
    (
        CONTAINERTYPE LPAREN y = varId RPAREN  
        {  
            tr = TypeResolver.createContainerTypeResolver((SchemaVariable)y); 
        } 
    )
;

varcond_new [TacletBuilder b]
:
   NEW LPAREN x=varId COMMA
      (
          TYPEOF LPAREN y=varId RPAREN {
	    b.addVarsNew((SchemaVariable) x, (SchemaVariable) y);
	  }
      |
         DEPENDINGON LPAREN y=varId RPAREN {
	    b.addVarsNewDependingOn((SchemaVariable)x, (SchemaVariable)y);
	  }
      | kjt=keyjavatype {
		b.addVarsNew((SchemaVariable) x, kjt.getJavaType());
	  }
      )
   RPAREN
   
;

varcond_newlabel [TacletBuilder b] 
:
  NEWLABEL LPAREN x=varId RPAREN {
     b.addVariableCondition(new NewJumpLabelCondition((SchemaVariable)x));
  }
;
varcond_typecheck [TacletBuilder b, boolean negated]
@init{
  TypeComparisonCondition.Mode mode = null;
}
:
   (  SAME  
      { 	
	  mode = negated 
	         ? TypeComparisonCondition.Mode.NOT_SAME 
	         : TypeComparisonCondition.Mode.SAME;
      } 
    | ISSUBTYPE 
      { 
          mode = negated 
                 ? TypeComparisonCondition.Mode.NOT_IS_SUBTYPE
                 : TypeComparisonCondition.Mode.IS_SUBTYPE; 
      }
    | STRICT ISSUBTYPE 
      {
          if(negated) {  
	      semanticError("A negated strict subtype check does not make sense.");
	  } 
	  mode = TypeComparisonCondition.Mode.STRICT_SUBTYPE;
      }
    | DISJOINTMODULONULL 
      {
          if(negated) {
              semanticError("Negation not supported");
          }
          mode = TypeComparisonCondition.Mode.DISJOINTMODULONULL;
      }
   ) 
   LPAREN fst = type_resolver COMMA snd = type_resolver RPAREN 
   {
	b.addVariableCondition(new TypeComparisonCondition(fst, snd, mode));
   }
;


varcond_free [TacletBuilder b]
:
   NOTFREEIN LPAREN x=varId COMMA ys=varIds RPAREN {
     Iterator it = ys.iterator();
     while(it.hasNext()) {
        b.addVarsNotFreeIn((SchemaVariable)x,(SchemaVariable)it.next());
     }
   }
;


varcond_hassort [TacletBuilder b]
@init{
  boolean elemSort = false;
}
:
   HASSORT 
   LPAREN 
   (x=varId | ELEMSORT LPAREN x=varId RPAREN {elemSort = true;}) 
   COMMA 
   s=any_sortId_check[true] 
   RPAREN 
   {
     if(!(s instanceof GenericSort)) {
   	 throw new GenericSortException("sort",
   					"Generic sort expected", 
   					s,
   					getSourceName(),
   					getLine(), 
   					getColumn());
     } else if (!JavaTypeToSortCondition.checkSortedSV((SchemaVariable)x)) {
   	 semanticError("Expected schema variable of kind EXPRESSION or TYPE, " 
   	 	       + "but is " + x);
     } else {
         b.addVariableCondition(new JavaTypeToSortCondition((SchemaVariable)x, 
     							    (GenericSort)s,
     							    elemSort));
     }
   }
;

varcond_fieldtype [TacletBuilder b]
:
    FIELDTYPE
    LPAREN
    x=varId
    COMMA 
    s=any_sortId_check[true] 
    RPAREN
    {
        if(!(s instanceof GenericSort)) {
            throw new GenericSortException("sort",
                                        "Generic sort expected", 
                                        s,
                                        getSourceName(),
                                        getLine(), 
                                        getColumn());
        } else if(!FieldTypeToSortCondition.checkSortedSV((SchemaVariable)x)) {
            semanticError("Expected schema variable of kind EXPRESSION or TYPE, " 
                          + "but is " + x);
        } else {
            b.addVariableCondition(new FieldTypeToSortCondition((SchemaVariable)x, 
                                                               (GenericSort)s));
        }
    }
;      

varcond_enumtype [TacletBuilder b, boolean negated]
:
   ISENUMTYPE LPAREN tr = type_resolver RPAREN
      {
         b.addVariableCondition(new EnumTypeCondition(tr, negated));
      }
;
 

varcond_reference [TacletBuilder b, boolean isPrimitive]
@init{
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

varcond_thisreference [TacletBuilder b, boolean negated]
@init {
  x = null;
  String id = null;
  boolean nonNull = false;
}
:
   ISTHISREFERENCE
   LPAREN      
     x = varId                           
   RPAREN 
   { b.addVariableCondition(new IsThisReference(x, negated)); }
;

        
varcond_staticmethod [TacletBuilder b, boolean negated]
:
   STATICMETHODREFERENCE LPAREN x=varId COMMA y=varId COMMA z=varId RPAREN {
      b.addVariableCondition(new StaticMethodCondition
         (negated, (SchemaVariable)x, (SchemaVariable)y, (SchemaVariable)z));
   }
;

varcond_referencearray [TacletBuilder b, boolean primitiveElementType]
:
   ISREFERENCEARRAY LPAREN x=varId RPAREN {
     b.addVariableCondition(new ArrayComponentTypeCondition(
       (SchemaVariable)x, !primitiveElementType));
   }
;

varcond_array [TacletBuilder b, boolean negated]
:
   ISARRAY LPAREN x=varId RPAREN {
     b.addVariableCondition(new ArrayTypeCondition(
       (SchemaVariable)x, negated));
   }
;

varcond_array_length [TacletBuilder b, boolean negated]
:
   ISARRAYLENGTH LPAREN x=varId RPAREN {
     b.addVariableCondition(new ArrayLengthCondition (
       (SchemaVariable)x, negated));
   }
;


varcond_abstractOrInterface [TacletBuilder b, boolean negated]
:
   IS_ABSTRACT_OR_INTERFACE LPAREN tr=type_resolver RPAREN {
     b.addVariableCondition(new AbstractOrInterfaceType(tr, negated));
   }
;

varcond_enum_const [TacletBuilder b]
:
   ENUM_CONST LPAREN x=varId RPAREN {
      b.addVariableCondition(new EnumConstantCondition(
	(SchemaVariable) x));     
   }
;

varcond_static [TacletBuilder b, boolean negated]
:
   STATIC LPAREN x=varId RPAREN {
      b.addVariableCondition(new StaticReferenceCondition(
	(SchemaVariable) x, negated));     
   }
;

varcond_localvariable [TacletBuilder b, boolean negated]
:
   ISLOCALVARIABLE 
	LPAREN x=varId RPAREN {
     	   b.addVariableCondition(new LocalVariableCondition((SchemaVariable) x, negated));
        } 
;


varcond_observer [TacletBuilder b]
:
   ISOBSERVER 
	LPAREN obs=varId COMMA heap=varId  RPAREN {
     	   b.addVariableCondition(new ObserverCondition((TermSV)obs, 
     	                                                (TermSV)heap));
        } 
;


varcond_different [TacletBuilder b]
:
   DIFFERENT 
	LPAREN var1=varId COMMA var2=varId RPAREN {
     	   b.addVariableCondition(new DifferentInstantiationCondition(
     	   				(SchemaVariable)var1,
     	   				 (SchemaVariable)var2));
        } 
;


varcond_metadisjoint [TacletBuilder b]
:
   METADISJOINT 
	LPAREN var1=varId COMMA var2=varId RPAREN {
     	   b.addVariableCondition(new MetaDisjointCondition(
     	   				(TermSV)var1,
     	   				(TermSV)var2));
        } 
;



varcond_equalUnique [TacletBuilder b]
:
   EQUAL_UNIQUE 
	LPAREN t=varId COMMA t2=varId COMMA phi=varId RPAREN {
     	   b.addVariableCondition(new EqualUniqueCondition((TermSV) t, 
     	                                                   (TermSV) t2, 
     	                                                   (FormulaSV) phi));
        } 
;


varcond_freeLabelIn [TacletBuilder b, boolean negated]
:

 FREELABELIN 
    LPAREN l=varId COMMA statement=varId RPAREN {
    	b.addVariableCondition(new FreeLabelInVariableCondition((SchemaVariable) l, 
    	(SchemaVariable) statement, negated ));
    }
;

varcond_constant [TacletBuilder b, boolean negated]
:
   ISCONSTANT
        LPAREN x=varId RPAREN {
           if (x instanceof TermSV) {
                b.addVariableCondition(new ConstantCondition((TermSV) x, negated ));
           } else {
                assert x instanceof FormulaSV;
                b.addVariableCondition(new ConstantCondition((FormulaSV) x, negated ));
           }
        }
;

varcond_label [TacletBuilder b, boolean negated]
:
   HASLABEL
        LPAREN l=varId COMMA name=simple_ident RPAREN {
           b.addVariableCondition(new TermLabelCondition((TermLabelSV) l, name, negated ));
        }
;

varcond_static_field [TacletBuilder b, boolean negated]
:
   ISSTATICFIELD
        LPAREN field=varId RPAREN {
           b.addVariableCondition(new StaticFieldCondition((SchemaVariable) field, negated ));
        }
;

varcond_subFormulas [TacletBuilder b, boolean negated]
:
   HASSUBFORMULAS
        LPAREN x=varId RPAREN {
           b.addVariableCondition(new SubFormulaCondition((FormulaSV) x, negated ));
        }
;

goalspecs[TacletBuilder b, boolean ruleWithFind] :
        CLOSEGOAL
    | goalspecwithoption[b, ruleWithFind] ( SEMI goalspecwithoption[b, ruleWithFind] )* ;

goalspecwithoption[TacletBuilder b, boolean ruleWithFind]
@init{
    soc = DefaultImmutableSet.<Choice>nil();
} :
        (( soc = option_list[soc]
                LBRACE
                goalspec[b,soc,ruleWithFind] 
                RBRACE)
        |  
            goalspec[b,null,ruleWithFind] 
        )
    ;

option returns [Choice c=null]
:
        cat=IDENT COLON choice_=IDENT
        {
            c = (Choice) choices().lookup(new Name(cat.getText()+":"+choice_.getText()));
            if(c==null) {
                throw new NotDeclException
			("Option", choice_.getText(), getSourceName(), choice_.getLine(), choice_.getCharPositionInLine());
	    }
        }
    ;
    
option_list[ImmutableSet<Choice> soc] returns [ImmutableSet<Choice> result = null]
:
LPAREN {result = soc; } 
  c = option {result = result.add(c);}
  (COMMA c = option {result = result.add(c);})*
RPAREN
;

goalspec[TacletBuilder b, ImmutableSet<Choice> soc, boolean ruleWithFind] 
@init{
    addSeq = Sequent.EMPTY_SEQUENT;
    addRList = ImmutableSLList.<Taclet>nil();
    addpv = DefaultImmutableSet.<SchemaVariable>nil();
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

replacewith returns [Object _replace_with]
@after{ _replace_with = o; }
:
        REPLACEWITH LPAREN o=termorseq RPAREN;

add returns [Sequent _add]
@after{ _add = s; }
:
        ADD LPAREN s=seq RPAREN;

addrules returns [ImmutableList<Taclet> _add_rules]
@after{ _add_rules = lor; }
:
        ADDRULES LPAREN lor=tacletlist RPAREN;

addprogvar returns [ImmutableSet<SchemaVariable> _add_prog_var]
@after{ _add_prog_var = pvs; }
:
        ADDPROGVARS LPAREN pvs=pvset RPAREN;

tacletlist returns [ImmutableList<Taclet> _taclet_list]
@init{ 
    lor = ImmutableSLList.<Taclet>nil(); 
}
@after{ _taclet_list = lor; }
    :
        head=taclet[DefaultImmutableSet.<Choice>nil()]   
        ( /*empty*/ | COMMA lor=tacletlist) { lor = lor.prepend(head); }
    ;

pvset returns [ImmutableSet<SchemaVariable> _pv_set] 
@init{
    pvs = DefaultImmutableSet.<SchemaVariable>nil();
}
@after{ _pv_set = pvs; }
    :
        pv=varId
        ( /*empty*/ | COMMA pvs=pvset) { pvs = pvs.add
                                          ((SchemaVariable)pv); };

rulesets returns [Vector rs = new Vector()] :
        HEURISTICS LPAREN ruleset[rs] ( COMMA ruleset[rs] ) * RPAREN ;

ruleset[Vector rs]
:
        id=IDENT
        {   
            RuleSet h = (RuleSet) ruleSets().lookup(new Name(id.getText()));
            if (h == null) {
                throw new NotDeclException("ruleset", id.getText(), getSourceName(), id.getLine(), id.getCharPositionInLine());
            }
            rs.add(h);
        }
    ;

metaId returns [TermTransformer v = null] 
:
  id = simple_ident {
     v = AbstractTermTransformer.name2metaop(id);
     if (v == null)
       semanticError("Unknown metaoperator: "+id);
  }
;

metaTerm returns [Term result = null]
@init{
    LinkedList al = new LinkedList();
} 
    :
        (vf = metaId 
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
                result = getTermFactory().createTerm(vf, (Term[])al.toArray(AN_ARRAY_OF_TERMS));
            }         
        ) 
 ;
     catch [TermCreationException ex] {
         keh.reportException
	    (new KeYSemanticException(input, getSourceName(), ex));
        }

contracts
:
   CONTRACTS
       LBRACE {
	    switchToNormalMode();
       }
       ( one_contract )*
       RBRACE 
;

invariants
@init{
  Namespace orig = variables();  
}
:
   INVARIANTS LPAREN selfVar=one_logic_bound_variable RPAREN
       LBRACE {
	    switchToNormalMode();
       }
       ( one_invariant[(ParsableVariable)selfVar] )*
       RBRACE  {
           unbindVars(orig);
       }
;


one_contract 
@init{
  String displayName = null;
  Vector rs = null;
  NamespaceSet oldServicesNamespaces = null;
}
:
   contractName = simple_ident LBRACE 
     { 
        //for program variable declarations
        namespaces().setProgramVariables(new Namespace(programVariables()));    
     }
     (prog_var_decls)? 
     fma = formula MODIFIES modifiesClause = term
     {
       DLSpecFactory dsf = new DLSpecFactory(getServices());
       try {
         contracts = contracts.add(dsf.createDLOperationContract(contractName,
       					                         fma, 
           				                         modifiesClause));
       } catch(ProofInputException e) {
         semanticError(e.getMessage());
       }
     } 
     RBRACE SEMI 
     {
       //dump local program variable declarations
       namespaces().setProgramVariables(programVariables().parent());
     }
;

one_invariant[ParsableVariable selfVar]
:
     invName = simple_ident LBRACE 
     fma = formula
     (DISPLAYNAME displayName = string_literal)?
     {
       DLSpecFactory dsf = new DLSpecFactory(getServices());
       try {
         invs = invs.add(dsf.createDLClassInvariant(invName,
                                                    displayName,
                                                    selfVar,
                                                    fma));
       } catch(ProofInputException e) {
         semanticError(e.getMessage());
       }
     } RBRACE SEMI
;

problem returns [ Term _problem = null ]
@init{
    choices=DefaultImmutableSet.<Choice>nil();
    chooseContract = this.chooseContract;
    proofObligation = this.proofObligation;
}
@after { _problem = a; this.chooseContract = chooseContract; this.proofObligation = proofObligation; }
    :
       { if (capturer != null) capturer.mark(); }

     profile

   	{ if (profileName != null && capturer != null) capturer.mark(); }

        (pref = preferences)
        { if ((pref!=null) && (capturer != null)) capturer.begin(); }
        


        string = bootClassPath
        // the result is of no importance here (strange enough)        
        
        stlist = classPaths 
        string = javaSource

        decls
        { 
            if(parse_includes || onlyWith) return null;
            switchToNormalMode();
        }

        // WATCHOUT: choices is always going to be an empty set here,
	// isn't it?
	( contracts )*
	( invariants )*
        (  RULES (choices = option_list[choices])?
	    LBRACE
            { 
                switchToSchemaMode(); 
            }
            ( 
                s = taclet[choices] SEMI
                {
                        if (!skip_taclets) {
                            final RuleKey key = new RuleKey(s); 
                            if (taclets.containsKey(key)) {
	                        semanticError
        	                ("Cannot add taclet \"" + s.name() + 
                	            "\" to rule base as a taclet with the same "+
                        	    "name already exists.");
                            	
                            } else {
                            	taclets.put(key, s);
                            }
                        }
                }
            )*
            RBRACE {choices=DefaultImmutableSet.<Choice>nil();}
        ) *
        { if (capturer != null) capturer.capture(); }
        ((PROBLEM LBRACE 
            {switchToNormalMode(); 
	     //if (capturer != null) capturer.capture();
	    }
                a = formula
            RBRACE) 
           | 
           CHOOSECONTRACT (chooseContract=string_literal SEMI)?
           {
	       if (capturer != null) {
	            capturer.capture();
	       }
	       if(chooseContract == null) {
	           chooseContract = "";
	       }
           }
           | 
           PROOFOBLIGATION  (proofObligation=string_literal SEMI)?
           {
               if (capturer != null) {
                    capturer.capture();
               }
               if(proofObligation == null) {
                   proofObligation = "";
               }
           }
	)?
   ;
   
bootClassPath returns [String _boot_class_path = null]
@after{ _boot_class_path = id; }
:
  ( BOOTCLASSPATH id=string_literal SEMI)? ;
   
classPaths returns [ImmutableList<String> ids = ImmutableSLList.<String>nil()]
:
  ( (
    CLASSPATH 
    s=string_literal {
      ids = ids.append(s);
    }
    SEMI
    )
  | 
    (
    NODEFAULTCLASSES {
      throw new NoViableAltException("\\noDefaultClasses is no longer supported. Use \\bootclasspath. See docs/README.classpath", -1, -1, input);
    }
    SEMI
    )
  )*
  ;

javaSource returns [String _java_source = null]
@after { _java_source = result; }
:
   (JAVASOURCE 
      result = oneJavaSource
    SEMI)?
    ;


oneJavaSource returns [String s = null]
@init{
  StringBuffer b=new StringBuffer();
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


profile:
        (PROFILE profileName=string_literal SEMI)? 
;

preferences returns [String _preferences = null]
@after{ _preferences = s; }:
	( KEYSETTINGS LBRACE
		(s = string_literal)?
		RBRACE )?
	;
	
proof [IProofFileParser prl] :
        ( PROOF proofBody[prl] )?
    ;


proofBody [IProofFileParser prl] :
        LBRACE
            ( pseudosexpr[prl] )+ 
        RBRACE
    ;


pseudosexpr [IProofFileParser prl] @init{ eid='0'; str = ""; } :
        LPAREN (eid=expreid
            (str = string_literal )? 
               { prl.beginExpr(eid,str); } 
            ( pseudosexpr[prl] )* ) ?
               { prl.endExpr(eid, stringLiteralLine); }
        RPAREN   
    ;

expreid returns [ char eid = '0' ]
:
   id = simple_ident {
      Character c = prooflabel2tag.get(id);
      if(c != null)
         eid = c.charValue();
   }
;
