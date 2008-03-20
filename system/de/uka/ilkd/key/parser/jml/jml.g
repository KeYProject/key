// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


/* -*-antlr-*- */
header {
    package de.uka.ilkd.key.parser.jml;

    import de.uka.ilkd.key.jml.*;
    
    import de.uka.ilkd.key.logic.*;
    import de.uka.ilkd.key.logic.sort.*;
    import de.uka.ilkd.key.logic.op.*;
    import de.uka.ilkd.key.collection.*;
    import de.uka.ilkd.key.util.ExtList;
    import de.uka.ilkd.key.gui.Main;
    import de.uka.ilkd.key.java.abstraction.*;
    import java.util.HashMap;
    import java.util.LinkedHashMap;
    import java.util.LinkedList;

    import de.uka.ilkd.key.collection.SetAsListOfString;
    import de.uka.ilkd.key.collection.SetOfString;
    import de.uka.ilkd.key.java.*;
    import de.uka.ilkd.key.java.abstraction.*;
    import de.uka.ilkd.key.java.declaration.*;
    import de.uka.ilkd.key.java.declaration.modifier.*;
    import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
    import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
    import de.uka.ilkd.key.java.reference.ReferencePrefix;
    import de.uka.ilkd.key.java.reference.TypeRef;
    import de.uka.ilkd.key.java.statement.BranchStatement;
    import de.uka.ilkd.key.java.statement.For;
    import de.uka.ilkd.key.java.statement.LoopStatement;
    import de.uka.ilkd.key.jml.*;
    import de.uka.ilkd.key.logic.*;
    import de.uka.ilkd.key.logic.op.*;
    import de.uka.ilkd.key.logic.sort.*;
    import de.uka.ilkd.key.parser.KeYSemanticException;
    import de.uka.ilkd.key.parser.NotDeclException;
    import de.uka.ilkd.key.util.ExtList;
}


class KeYJMLParser extends Parser;
options {
	importVocab=KeYJMLLexer;
	k = 1;
	defaultErrorHandler=true;
}

{
  
    static int paramVarCount = 0;
    static int mmCount = 0;
    private JMLTranslator translator;
    private ArithOpProvider aOP;
    private SetOfJMLMethodSpec specs = SetAsListOfJMLMethodSpec.EMPTY_SET;
    private TermFactory tf;
    private TermBuilder df;
    private NamespaceSet nss;
    private ProgramMethod md;
    private JMLClassSpec cSpec;

    //the namespace for the methodparameters.
    private Namespace param_ns = new Namespace();
    //mapping of expression to a term representing their evaluation in the pre
    //state. Needed for the \old construct.
    private LinkedHashMap term2old = new LinkedHashMap();
    //used for caching of the result variable delivered by JMLMethodSpec
    private ProgramVariable result;
    //used to cache the KeYJavaType of a term. Ugly, should be implemented
    //in a different way.
    private KeYJavaType tempkjt = null;
    private String methodname = null;
    private Term BOOL_TRUE;
    private Term BOOL_FALSE;
    private boolean preMode = true;
    private boolean staticMode = false;
    private LinkedHashMap variable2term;
    // a dummy term to get rid of some warnings
    private Term dummy;
    // a dummy KeYJavaType to get rid of some warnings
    private KeYJavaType dt;
    private String dummyString;
    private JMLSpec currentSpec = null;

    //used for parsing packagereferences
    private String packageName = "";
    
    // the path where the sources are located
    private String javaPath;

    private int lineOffset=0;
    private int colOffset=0;
    
    private boolean isOldAllowed = true;
    private boolean inOld = false;
    
    private Services services;
    
    private Term quantifiedArrayGuard = null;

    public KeYJMLParser(TokenStream lexer, String filename, 
    	Services services, NamespaceSet nss, TermFactory tf, TypeDeclaration cld, 
        ProgramMethod pm, JMLClassSpec cSpec, ArithOpProvider aOP,
        String javaPath){
	
	this(lexer);
        setFilename(filename);
        this.cSpec = cSpec;
        currentSpec = cSpec;
        this.nss = nss;
        this.services = services;
        this.tf = tf;
        this.df = TermBuilder.DF;
        this.md = pm;        
        staticMode = md != null && md.isStatic();
        this.aOP = aOP;
        this.translator = new JMLTranslator(cld, services, this, aOP);      
        variable2term = new LinkedHashMap();
        param_ns = UsefulTools.buildParamNamespace(md!=null ? 
                                                   md.getMethodDeclaration() : null);
        BOOL_TRUE = services.getTypeConverter()
            .convertToLogicElement(BooleanLiteral.TRUE); 
        BOOL_FALSE = services.getTypeConverter()
            .convertToLogicElement(BooleanLiteral.FALSE); 

        this.javaPath=javaPath;
        
        if (javaPath == null) {
            de.uka.ilkd.key.util.Debug.printStackTrace();
        }
    }

    public KeYJMLParser(TokenStream lexer, String filename, 
    	Services services, NamespaceSet nss, TermFactory tf, JMLClassSpec cSpec, 
        ArithOpProvider aOP, String javaPath){
	    this(lexer, filename, services, nss, tf, null, null, cSpec, aOP, javaPath);
    }

    public void reportError(RecognitionException ex){
        if(ex instanceof NotSupportedExpressionException){
            if(!((NotSupportedExpressionException) ex).canBeIgnored()){
                currentSpec.setInvalid((NotSupportedExpressionException) ex);
            }
            if(currentSpec instanceof LoopInvariant){
				//if the specification for loop contains 
				// unsupported expressions we discard it.
				services.getImplementation2SpecMap().
				clearSpecsForLoop(((LoopInvariant) currentSpec).getLoop());
                System.out.println("Unsupported Expression in loop Invariant: "
                                   + ex);
            }
        }
        services.getExceptionHandler().reportException(ex);
    }

    public LoopInvariant parseLoopInvariant(LoopStatement loop) 
        throws antlr.ANTLRException{
        setPrefix(cSpec.getInstancePrefix());
        LoopInvariant l = 
            services.getImplementation2SpecMap().getSpecForLoop(loop);
        if(l == null){
            l = new LoopInvariant(loop, services, (ProgramVariable)cSpec.getInstancePrefix());
        }
        param_ns = new Namespace(param_ns);
        Namespace ns = collectLocalVariables(loop, md.getMethodDeclaration().getBody());
        if(ns != null){
            param_ns.add(ns);
        }
        loop_spec(l);
        l.register();
        return l;
    }

    private KeYJavaType getArrayTypeAndEnsureExistence(Sort baseSort,
                                                       int dim){
        return translator.getArrayTypeAndEnsureExistence(baseSort, dim);
    }

    /**
     * Collects local variables of b that are visible for the statement loop.
     * Returns null if loop has not been found
     */
    private Namespace collectLocalVariables(LoopStatement loop, 
                                            StatementContainer b){
        Namespace ns = new Namespace();
        Statement s;
        for(int i = 0; i<b.getStatementCount(); i++){
            s = b.getStatementAt(i);
            if(s == loop){
                if(loop instanceof For){
                    for(int j = 0; loop.getInitializers() != null && 
                        j<loop.getInitializers().size(); j++){
                        if(loop.getInitializers().getLoopInitializer(j) 
                            instanceof LocalVariableDeclaration){
                        ArrayOfVariableSpecification vars = 
                            ((LocalVariableDeclaration) 
                            loop.getInitializers().getLoopInitializer(j)).
                                getVariables();
                        for(int k=0; k<vars.size(); k++){
                                ns.add(vars.getVariableSpecification(k).
                                    getProgramVariable());
                            }
                        }
                    }
                }
                return ns;
            }
            if(s instanceof LocalVariableDeclaration){
                ArrayOfVariableSpecification vars = 
                    ((LocalVariableDeclaration) s).getVariables();
                for(int j=0; j<vars.size(); j++){
                    ns.add(vars.getVariableSpecification(j).getProgramVariable());
                }
            }
            if(s instanceof StatementContainer){
                Namespace n = collectLocalVariables(loop, 
                                                    (StatementContainer) s);
                if(n != null){ 
                    ns.add(n);
                    return ns;
                }
            }
            if(s instanceof BranchStatement){
                for(int j=0; j < ((BranchStatement) s).getBranchCount(); j++){
                    Namespace n = collectLocalVariables(loop, 
                        ((BranchStatement) s).getBranchAt(j));
                    if(n != null){ 
                        ns.add(n);
                        return ns;
                    }
                }
            }
        }
        return null;
    }

    private void addSpec(JMLMethodSpec s){
        specs = specs.add(s);
        term2old = s.getTerm2Old();
        currentSpec = s;
    }

    public LinkedHashMap term2old() {
	return term2old;
    }
	
    public String javaPath() {
	return javaPath;
    }

    //the prefix needed for attribute terms.
    public ReferencePrefix prefix() {
	return translator.prefix();
    }
	
    public void setPrefix(ReferencePrefix prefix) {
	translator.setPrefix(prefix);
    }
	
    public SetOfJMLMethodSpec getSpecs(){
        return specs;
    }

    private void setPreMode(boolean mode){
        preMode = mode;
    }

    private boolean inPreMode(){
        return preMode;
    }

    private Term lookupVar(Name name) throws KeYSemanticException{
        Named named = variables().lookup(name);
        if (named == null) {
            named = namespaces().programVariables().lookup(name);
        }

        boolean param = false;
        if (named == null) {
            named = param_ns == null ? null : param_ns.lookup(name);
            param = true;
        }
        if(named != null){
            if(named instanceof ProgramVariable){
                final ProgramVariable p = (ProgramVariable) named;
                if (inPreMode() || (!param || inOld)) {
                    return getTermForVariable(p);
                } else if (param && !inOld) {                     
                    return getOld(df.var(p));
                }                
            } else {
                return df.var((LogicVariable) named);
            }
        }
        return lookupAssignableVar(name);
    }

    private KeYJavaType getReferenceType(String n) throws NotDeclException{
        KeYJavaType kjt = getJavaInfo().getKeYJavaType(n);
        if(kjt==null){
            try{
                kjt = getJavaInfo().getTypeByClassName(n);
            }catch(RuntimeException e){
            }
            if (kjt==null){
                throw new NotDeclException("type", 
                    n, getFilename(), getLine(), getColumn());
            }
        }
        return kjt;
    }

    private Term getTermForVariable(ProgramVariable p){
        Term vt = (Term)variable2term.get(p);
        if (vt == null) {
            vt = df.var(p);
            variable2term.put(p, vt);
            
        }
        return vt;
    }

    /** In the assignable clause no parameters may occur.
     */  
    private Term lookupAssignableVar(Name name) throws KeYSemanticException{
        ProgramVariable v = null;
        try{
            if(cSpec.lookupModelField(name)!=null){
                v = (ProgramVariable) cSpec.lookupModelField(name);
                if (v.isStatic()){
                    return getTermForVariable(v);
                } else if(!staticMode){
                    return df.dot(getTermForVariable((ProgramVariable) cSpec.getInstancePrefix()), v);
                } else {
                    throw new KeYSemanticException("Nonstatic modelfield in"+
                    " static context", getLine(), getColumn(), getFilename());
                }
            }
        }catch(AmbigiousModelElementException e){
            System.err.println(e.toString());
        }
        // %%%RB this should be checked (model fields??)
        String attributeName = name.toString();
	if (attributeName.indexOf(':')!=-1) {
	  attributeName = attributeName.substring(attributeName.lastIndexOf(':') + 1);
	}
        v = getJavaInfo().lookupVisibleAttribute(name.toString(), 
                                                 translator.getCLDKeYJavaType()); 

        if(v == null) {
            return null;
        }
        
        if(v.isStatic()){
            return getTermForVariable(v);
        }else if(!staticMode){
            return df.dot(getTermForVariable((ProgramVariable) cSpec.getInstancePrefix()), v);
        }else{
            throw new KeYSemanticException("Nonstatic field "+name+
                " in static context", getLine(), getColumn(), getFilename());
        }
    }

  
    private Term getOld(Term t){
        return translator.getOld(t, currentSpec);       
    }

    public Term buildQuantifierTerm(String q, ListOfNamed l, Term a, Term t) 
    throws NotSupportedExpressionException {
    	return UsefulTools.addRepresents(translator.buildQuantifierTerm(q, l, a, t, currentSpec), services, null);
    }

    protected void bindVars(ListOfNamed l) {
        namespaces().setVariables(variables().extended(l));
    }

    protected void bindVar(Named n) {
        namespaces().setVariables(variables().extended(n));
    }

    protected void unbindVars() {
        namespaces().setVariables(variables().parent());
    }

    protected void bindProgVars(ListOfNamed l) {
        namespaces().setProgramVariables(namespaces().programVariables().extended(l));
    }

    protected void bindProgVars(Named n) {
        namespaces().setProgramVariables(namespaces().programVariables().extended(n));
    }

    protected void unbindProgVars() {
        namespaces().setProgramVariables(namespaces().programVariables().parent());
    }


    /** We have to replace arguments of functions that have been translated to
     * formulas. Usually this is done by a query, however in simple cases
     * like <code>a</code> == true which can be simplified to <code>a</code>
     * a query isn't necessary.
     * @returns a simplification of <code>arg</code> in some special cases
     * or <code>arg</code> otherwise.
     */
    protected Term simplifyArgument(Term arg){
        if (arg.op() == Op.TRUE){
            return BOOL_TRUE;
        }
        if (arg.op() == Op.FALSE){
            return BOOL_FALSE;
        }
        if(arg.op() instanceof Equality){            
            if (arg.sub(0) == BOOL_TRUE || arg.sub(0).op() == Op.TRUE){
                return simplifyArgument(arg.sub(1));
            }
            if(arg.sub(1) == BOOL_TRUE || arg.sub(1).op() == Op.TRUE){
                return simplifyArgument(arg.sub(0));
            }
        }
        return arg;
    }

    private ListOfKeYJavaType getTypeList(ListOfTerm tl){
    final TypeConverter typeConverter = services.getTypeConverter();
        final Sort intSort = typeConverter.getIntegerLDT().targetSort(); 
        final Sort intDomainSort = typeConverter.getIntegerDomainLDT().targetSort(); 
        IteratorOfTerm it = tl.iterator();
        ListOfKeYJavaType sig = SLListOfKeYJavaType.EMPTY_LIST;
        Term temp;
        while(it.hasNext()){
            temp = it.next();
            if(temp.sort() == Sort.FORMULA){
                sig = sig.append(getJavaInfo().getKeYJavaType(
                        PrimitiveType.JAVA_BOOLEAN));
            }else{
                KeYJavaType sigkjt=null;
                try{
                    sigkjt = services.getTypeConverter().
                    getKeYJavaType(temp);
                }catch(Exception e){}
                if(sigkjt == null){
                    if (temp.sort() == intSort || temp.sort() == intDomainSort) {
                    // these sorts have no integer domain
                    	sigkjt = getJavaInfo().getKeYJavaType(typeConverter.getIntLDT().targetSort());
		    } else {
                        sigkjt = getJavaInfo().getKeYJavaType(temp.sort());
                    }
                   
                }
                sig = sig.append(sigkjt);
            }
        }
        return sig;
    }

    /** 
     * returns the translation of \\nonnullelements(t).
     */
    protected Term nonNullElements(Term t){
       return translator.nonNullElements(t, currentSpec);
    } 

     /**
     * creates a model method and adds it to the class specification
     */   
    protected Term createModelMethod(String name, Term result, Term pre, Term post){
    	return translator.createModelMethod(name, result, pre, post, cSpec, staticMode);
    }	
  
    private boolean isLong(Term t){
        return translator.isLong(t);
    }

	public JavaInfo getJavaInfo() {
	    return getServices().getJavaInfo();
    }

	public Services getServices() {
	    return services;
    }

    public NamespaceSet namespaces(){
        return nss;
    }

    public Namespace sorts() {
        return namespaces().sorts();
    }

    public Namespace variables() {
        return namespaces().variables();
    }
    
    public Namespace functions() {
        return namespaces().functions();
    }

    public Namespace choices(){
        return namespaces().choices();
    }

    public void parseClassSpec() throws antlr.ANTLRException {
        top();
    }

    public void parseMethodDecl(String comments) throws antlr.ANTLRException {
        methoddecl2(comments);        
    }

    public void parseFieldDecl() throws antlr.ANTLRException {
        field();        
    }

    public Term toZNotation(String s){              
        Term number;

        final Function numberTerminator = (Function) functions().lookup(new Name("#"));
        number = df.func(numberTerminator);
        
        Function numberSymbol = (Function) functions().lookup(new Name(s.substring(0,1)));
        number = df.func(numberSymbol, number);
        
        for(int i=1; i<s.length(); i++){                
            numberSymbol = (Function)functions().lookup(new Name(s.substring(i,i+1)));
            number = df.func(numberSymbol, number);
        }          

        final Function Z = (Function) functions().lookup(new Name("Z"));        
        return df.func(Z, number);        
    }

    protected int getLine() {
        int line = -1;
        try {
            line = LT(0).getLine()+lineOffset;
        } catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return line;
    }

    protected int getColumn() {
        int 	col = -1;
        try {
            col = LT(0).getColumn()+colOffset;
        } 
        catch (TokenStreamException e) {
            System.err.println("No further token in stream");
        }
        return col;
    }   

    protected static class ArraySpecIndexBound {
        private Term lower;
        private Term upper;
        private boolean starQuantification;

        public void setLower(Term t) {
            this.lower = t;
        }

        public void setUpper(Term t) {
            this.upper = t;
        }

        public void setStar(boolean b) {
            this.starQuantification = b;
        }

        public Term lower() {
            return lower;
        }

        public Term upper() {
            return upper;
        }

        public boolean isStar() {
            return starQuantification;
        }
        
        public boolean singleValue() {
            return lower != null && upper == null && !isStar();
        }

    }

}

top : 
        // parses the pure modifier in cases in which it refers to a type declaration 
        ("pure") => "pure"
        {
            services.getImplementation2SpecMap().setPure(translator.getCLDKeYJavaType(),
							 nss, javaPath);
        }
    |   
        (field)*
    ;

loop_spec [LoopInvariant l]
{
    this.term2old = l.getTerm2Old();
    isOldAllowed = false;
}:
        (   
            "set"
            {
                throw new NotSupportedExpressionException("set", true);
            }
        |
            loop_invariant[l]
        |
            assignableclause[l]
        |
            variant_function[l]
        |
            loop_post[l]
        )+
        { isOldAllowed = true; }
    ;

loop_post[LoopInvariant l] 
{
    Term t=null; 
}:
        ensureskeyword {setPreMode(false);} t=predornot 
        {
            if(t!=null) l.addPost(t); 
        } 
        ";"
    ;

loop_invariant[LoopInvariant l]
{
    Term t;
}:
        maintaining_keyword t = predicate ";"
        {
            l.addInvariant( df.and(t, df.func(getJavaInfo().getInReachableState())) );
        }
;

maintaining_keyword :
        "maintaining" 
    | 
        "maintaining_redundantly"
    | 
        "loop_invariant" 
    | 
        "loop_invariant_redundantly"
;

variant_function[LoopInvariant l] 
{
    Term t;
}: 
        decreasing_keyword t=specexpression ";"
        {
            l.setVariant(t);
        }
    ;

decreasing_keyword : 
        "decreasing" 
    | 
        "decreasing_redundantly"
    | 
        "decreases" 
    | 
        "decreases_redundantly"
    ;



field 
{
    SetOfString mods=SetAsListOfString.EMPTY_SET;
}: 
        {
         term2old = cSpec.getTerm2Old(); 
         setPrefix(cSpec.getInstancePrefix());}
        (
            (("model")? "import") => import_definition
        |
            (
                mods=modifiers
                (
                    jmldeclaration[mods]
                |
                    memberdecl[mods]
                )
            )
        )
    ;

import_definition :
        ("model")? "import" name_star ";"
    ;

name_star :
        IDENT (DOT (IDENT | MULT))*
    ;

memberdecl[SetOfString mods] :
        variabledecls[mods]
    ;

//not used due to the necessity that the methoddeclaration has to be parsed
//before the method specification
//methoddecl :
//        methodspecification 
//        methoddecl2[""]
//        {
//            addMethod2Specs();
//        }
//;

methoddecl2[String comments]
{
    KeYJavaType type = null;
    KeYJavaType dummyType;
    SetOfString mods=SetAsListOfString.EMPTY_SET;
}:
        mods=modifiers 
        (
            (type IDENT) => type=typespec
        )? 
        methodhead[type, mods, comments] 
        // "throws" is ignored 
        (THROWS dummyType=type ("," dummyType=type)*)?
        (
            ";"
        |
            LBRACE
            {
                throw new NotSupportedExpressionException(
                    "Implementation for modelmethod");
            }
        )
    ;

methodhead[KeYJavaType type, SetOfString mods, String comments]
{
    LinkedList l = new LinkedList();
}:
        id:IDENT "(" (l = paramdeclarationlist)? ")"
        {
            ExtList el = new ExtList();
            if(comments != null){
                el.add(new Comment(comments));
            }
            el.add(new Public());
            if(mods.contains("static")){
                el.add(new Static());
            }
            if(mods.contains("private")){
                el.add(new Private());
            }else if(mods.contains("public")){
                el.add(new Public());
            }else if(mods.contains("protected")){
                el.add(new Protected());
            }
            el.add(new Model());
            Object[] oarr = l.toArray();  
            for(int i=0; i<oarr.length; i++){
                el.add((ParameterDeclaration) oarr[i]);
            }
            el.add(new ProgramElementName(id.getText()));
            MethodDeclaration mdecl;
            if(type != null){
                el.add(new TypeRef(type));
                mdecl = new MethodDeclaration(el, translator.isInterface());
            }else{
                type = getJavaInfo().getKeYJavaType("void");
                mdecl = new ConstructorDeclaration(el,translator.isInterface());
            }
            md = new ProgramMethod(mdecl, 
                                   translator.getCLDKeYJavaType(), 
                                   type, PositionInfo.UNDEFINED);
            if(mods.contains("pure")){
                services.getImplementation2SpecMap().addModifier(md, "pure");
            }
            if(mods.contains("helper")){
                if(!md.isPrivate()){
                    throw new KeYSemanticException("Helper methods must be "+
                        "private but "+md.getName()+" isn't", 
                        getLine(), getColumn(), getFilename());
                }
                services.getImplementation2SpecMap().addModifier(md, "helper");
            }
            cSpec.addModelMethod(md);
        }
;

paramdeclarationlist returns[LinkedList pl = new LinkedList()]
{
    ParameterDeclaration pd = null;
}:
        pd = paramdeclaration {pl.add(pd);} 
        ("," pd = paramdeclaration {pl.add(pd);})*
;

paramdeclaration returns[ParameterDeclaration pd = null]
{
    int dim = 0;
    KeYJavaType type;
}:
        //parameter modifiers are ignored at the moment
        (param_modifier)? type=typespec id:IDENT (dim=dims)?
        {
            ProgramVariable v = new LocationVariable(new ProgramElementName(
                id.getText()), type); 
            param_ns.add(v);
            pd = new ParameterDeclaration(new Modifier[0], 
                new TypeRef(type), new VariableSpecification(v), false);
        }
;

param_modifier:
        "final"
    |
        "non_null"
    ;

variabledecls[SetOfString mods]
{
    KeYJavaType type;
}:
        type=typespec variabledeclarators[type, mods] ";"
        ((jml_datagroup_clause) => jml_datagroup_clause)?
    ;

//datagroups
//not implemented --->
jml_datagroup_clause :
        in_group_clause | maps_into_clause
    ;

in_group_clause :
        in_keyword group_list ";" 
    ;

in_keyword :
        "in" | "in_redundantly"
    ;

group_list :
        group_name ("," group_name)*
    ;

group_name :
        (group_name_prefix)? IDENT
    ;

group_name_prefix :
        "this" DOT | "super" DOT
    ;

maps_into_clause :
        maps_keyword member_field_ref INTO group_list ";"
    ;

maps_keyword :
        "maps" | "maps_redundantly"
;

member_field_ref :
        (IDENT DOT) => IDENT DOT maps_member_ref_expr
    | 
        maps_array_ref_expr ( DOT maps_member_ref_expr )?
    ;

maps_member_ref_expr :
        IDENT | MULT 
    ;

maps_array_ref_expr :
        IDENT maps_spec_array_dim ( maps_spec_array_dim )* 
;

maps_spec_array_dim 
{
    ArraySpecIndexBound l;
}:
        "[" l = specarrayrefexpr[null] "]"
    ;

//   <---   not implemented

variabledeclarators[KeYJavaType type, SetOfString mods]:
        variabledeclarator[type, mods] ("," variabledeclarator[type, mods])*
    ;

variabledeclarator[KeYJavaType type, SetOfString mods]
{
    int dim = 0;
}:
        id:IDENT (dim=dims)?
        {
            if(dim!=0){
                type = getArrayTypeAndEnsureExistence(type.getSort(), dim);
            }

            cSpec.addModelVariable(new LocationVariable(
                    new ProgramElementName(id.getText()),type, 
                    translator.getCLDKeYJavaType(),
                    mods != null && mods.contains("static") ||
                        translator.isInterface() &&
                        !mods.contains("instance"),
                    mods.contains("model"), mods.contains("ghost")));
        }
    ;

modifiers returns[SetOfString mods=SetAsListOfString.EMPTY_SET]
{
    String m;
}:
        (m=modifier {mods = mods.add(m);})*
    ;

modifier returns[String s=null]:
        s=privacy
    |
        "instance" {s="instance"; setPrefix(cSpec.getInstancePrefix());}
    |
        "static" {s="static";}
    |
        "model" {s = "model";}
    |
        "pure" {s = "pure";}
    |
        "helper" {s = "helper";}
    | 
        "ghost" 
    | 
        "uninitialized"
    | 
        "spec_java_math" 
    | 
        "spec_safe_math" 
    | 
        "spec_bigint_math"
    | 
        "code_java_math" 
    | 
        "code_safe_math" 
    | 
        "code_bigint_math"
    | 
        "non_null"
    ;

privacy returns[String s=null]:
        "public" {s="public";}
    |
        "protected" {s="protected";}
    |       
        "private" {s="private";}
    |
        "spec_public" 
    | 
        "spec_protected"
    ;

jmldeclaration[SetOfString mods] : 
        invariant[mods]
    |
        historyconstraint[mods]
    |
        representsdecl[mods]
    | 
        initially_clause
    | 
        monitors_for_clause
    | 
        readable_if_clause
    | 
        writable_if_clause
    | 
        "axiom" dummy = predicate ";"
    |
        //HACK: jml-datagroup-clauses refering to a real field can occur here,
        //which doesn't harm right now as they are ignored anyway.
        jml_datagroup_clause
    ;

//not implemented --->
initially_clause :
        "initially" dummy = predicate ";"
    ;

readable_if_clause :
        "readable" IDENT "if" dummy = predicate ";"
    ;

writable_if_clause :
        "writable" IDENT "if" dummy = predicate ";"
    ;

monitors_for_clause : 
        "monitors_for" IDENT
        l_arrow_or_eq spec_expression_list ";"
    ;
//  <--- not implemented

representsdecl[SetOfString mods]
{
    Term t1,t2;
}:
        representskeyword t1=storerefexpression
        (
            l_arrow_or_eq t2=specexpression
            {
                cSpec.addRepresents(t1, t2);
            }
        |
            SUCH_THAT t2=predicate
            {
                cSpec.addSuchThat(t1, t2);
            }
        )
        ";"
    ;

representskeyword:
        "represents"
    |
        "represents_redundantly"
    ;

l_arrow_or_eq:
        "<-" 
    |
        "="
    ;

invariant[SetOfString mods]{
    Term t=null;
} :
        invariantkeyword 
        {
            if(mods.contains("static") || translator.isInterface() &&
               !mods.contains("instance")){
                staticMode = true;
            }else{
                staticMode = false;
            }
        }
        t=predicate ";"
        {
            if(staticMode){
                cSpec.addStaticInvariant(t);
            }else{
                cSpec.addInstanceInvariant(t);      
            } 
        }
    ;

invariantkeyword :
        "invariant" 
    |
        "invariant_redundantly" 
    ;

historyconstraint[SetOfString mods]{
    Term t=null;
} :
        constraintkeyword {staticMode = mods.contains("static");} 
        t=predicate ";"
        {
            if(mods.contains("static")){
                cSpec.addStaticConstraint(t);
            }else{
                cSpec.addInstanceConstraint(t);
            }
        }
    ;

constraintkeyword :
        "constraint" 
    |
        "constraint_redundantly"
    ;

methodspecification :
        (pure_helper) => (pure_helper)*
    |
        specification
    |
        extendingspecification
    |
        //HACK these tokens shouldn't occur in this place.
        "assume"
        {
            throw new NotSupportedExpressionException("assume", true);
        }    
    |
        "assert"
        {
            throw new NotSupportedExpressionException("assert", true);
        }
    |
        "nowarn"
        {
            throw new NotSupportedExpressionException("nowarn", true);
        } 
    |
        "set"
        {
            throw new NotSupportedExpressionException("set", true);
        }
    |
        jml_datagroup_clause
    ;

pure_helper 
{
    String p;
}:
        (p=privacy)?
       (
            "pure" 
            {
                if(!services.getImplementation2SpecMap().
                    getModifiers(md).contains("pure")){
                    new JMLPuritySpec(md, services, param_ns, 
                        term2old, cSpec, nss, javaPath);
                    services.getImplementation2SpecMap().
                        addModifier(md, "pure");
                }
            }
        |
            "helper" 
            {
                if(!md.isPrivate()){
                    throw new KeYSemanticException("Helper methods must be "+
                        "private but "+md.getName()+" isn't", 
                        getLine(), getColumn(), getFilename());
                }
                services.getImplementation2SpecMap().addModifier(md, "helper");
            }
        |
            "non_null"
            {
                JMLNormalMethodSpec s = new JMLNormalMethodSpec(
                    md, services, param_ns, term2old, cSpec, nss, javaPath);
                Term t = df.not(df.equals(df.var(s.getResultVar()), df.NULL(services)));               
                s.addPost(t);
            }
        )
    ;

extendingspecification :
        "also" specification
    ;

specification :
        speccaseseq (redundant_spec)?
    |
        redundant_spec
    ;

// redundant specifications are not supported 
//------------------>

//implementation not complete
redundant_spec :
        (
            implications 
        |
            examples
        )
        {
            throw new NotSupportedExpressionException(
                "redundant specification", true);
        }
    ;

examples :
        "for_example" 
    ;

implications :
        "implies_that" 
    ;
 // <-----------------

speccaseseq :
        speccase (ALSO speccase)*
    ;

speccase :
        ((dummyString=privacy)? "model_program") => model_program
    |
        lightweightspeccase
    |
        heavyweightspeccase
    |
        code_contract_spec
    ;

//not implemented --->
code_contract_spec : 
        "code_contract" (code_contract_clause)+
    ;

code_contract_clause :
        accessible_clause
    | 
        callable_clause
    | 
        measured_clause 
    ;

measured_clause :
        measured_by_keyword
        (
            NOT_SPECIFIED ";"
        |
            dummy=specexpression ( "if" dummy=predicate )? ";"
        )
    ;

measured_by_keyword :
        "measured_by" 
    |
        "measured_by_redundantly"
    ;

accessible_clause 
{
    SetOfLocationDescriptor locs;
}:
        accessible_keyword locs=conditionalstorereflist[null] ";"
    ;

accessible_keyword :
        "accessible" 
    |
        "accessible_redundantly"
    ;

callable_clause :
        callable_keyword callable_methods_list ";"
    ;

callable_keyword :
        "callable" 
    |
        "callable_redundantly"
    ;

callable_methods_list :
        method_name_list | dummyString=storerefkeyword[null]
    ;

method_name_list :
        method_name ( "," method_name )*
    ;

method_name :
        method_ref ( "(" ( param_disambig_list )? ")" )?
    ;

method_ref :
        method_ref_start ( DOT method_ref_rest )*
    | 
        "new" dt=referencetype
    ;

method_ref_start :
        "super" | "this" | IDENT | OTHER
    ;

method_ref_rest :
        "this" | IDENT | OTHER
    ;

param_disambig_list :
        param_disambig ( "," param_disambig )*
    ;

param_disambig 
{
    int d;
}:
        dt=typespec ( IDENT ( d=dims )? )?
    ;

model_program : 
        ( dummyString=privacy )? 
        {
            throw new NotSupportedExpressionException("Model Program");
        }
        "model_program" LBRACE
    ;

// <--- not implemented

lightweightspeccase 
{
    JMLMethodSpec s=new JMLMethodSpec(md, services, 
        param_ns, term2old, cSpec, nss, javaPath);
}:
        genericspeccase[s]
    ;

heavyweightspeccase 
{
    String p = null;
}:
        (p=privacy)?  
        (
            "normal_behavior" 
            normalspeccase[new JMLNormalMethodSpec(md, services, 
                    param_ns, term2old, cSpec, nss, javaPath)]
        |
            "behavior" genericspeccase[new JMLMethodSpec(md, 
                    services, param_ns, term2old, cSpec, nss, javaPath)]
        |
            "exceptional_behavior" 
            exceptionalspeccase[new JMLExceptionalMethodSpec(md, 
                    services, param_ns, term2old, cSpec, nss, javaPath)]
        )
    ;

genericspeccase [JMLMethodSpec s] 
{
    result = s.getResultVar();
    setPrefix(s.getPrefix());
    addSpec(s);
    ListOfNamed lvs=SLListOfNamed.EMPTY_LIST;
}:
        (lvs=spec_var_decls[s])?
        {
            s.setSpecVars(lvs);
            bindVars(lvs);
        }
        (
            specheader[s] (genericspecbody[s])? 
        |
            genericspecbody[s] 
        )
        {
            unbindVars();
        }
     ;

spec_var_decls[JMLMethodSpec s]  returns 
    [ListOfNamed lvs=SLListOfNamed.EMPTY_LIST]:
        (
            "old"
            {
                throw new NotSupportedExpressionException(
                    "Specification Variable Declaration");
            }
        |
            lvs=forall_var_decls[s]
        )
    ;

forall_var_decls[JMLMethodSpec s] returns 
    [ListOfNamed lvs=SLListOfNamed.EMPTY_LIST]
{
    LogicVariable lv;
}:
        (lv=forall_var_declarator[s] {lvs = lvs.append(lv);})+
    ;

forall_var_declarator[JMLMethodSpec s] returns [LogicVariable lv=null]
{
    KeYJavaType kjt;
} :
        "forall" kjt=typespec lv=quantifiedvariabledeclarator[kjt] ";"
;

normalspeccase [JMLNormalMethodSpec s]
{
    result = s.getResultVar();
    setPrefix(s.getPrefix());
    addSpec(s);
    ListOfNamed lvs=SLListOfNamed.EMPTY_LIST;
} :
        (lvs=spec_var_decls[s])?
        {
            s.setSpecVars(lvs);
            bindVars(lvs);
        }
        (
            specheader[s] (normalspecbody[s])?
        |
            normalspecbody[s]
        )
        {
            unbindVars();
        }
    ;

exceptionalspeccase [JMLExceptionalMethodSpec s] 
{
    result = s.getResultVar();
    setPrefix(s.getPrefix());
    addSpec(s);
    ListOfNamed lvs=SLListOfNamed.EMPTY_LIST;
} :
        (lvs=spec_var_decls[s])?
        {
            s.setSpecVars(lvs);
            bindVars(lvs);
        }
        (
            specheader[s] (exceptionalspecbody[s])?
        |
            exceptionalspecbody[s]
        )
        {
            unbindVars();
        }
    ;


specheader[JMLMethodSpec s] :
        requiresclause[s] (requiresclause[s])*
    ;
        
genericspecbody[JMLMethodSpec s] :
        simplespecbodyclause[s] (simplespecbodyclause[s])*
    |
        LBRACE "|" genericspeccaseseq[s] "|" RBRACE
    ;

genericspeccaseseq[JMLMethodSpec s] 
{
    JMLMethodSpec copy = s.copy();
    services.getImplementation2SpecMap().removeMethodSpec(copy);
}:
        genericspeccase[s] ( "also" genericspeccase[copy.copy()] )*
;

normalspecbody[JMLNormalMethodSpec s] :
        normalspecclause[s] (normalspecclause[s])*
    |
        LBRACE "|" normalspeccaseseq[s] "|" RBRACE
    ;

normalspeccaseseq[JMLNormalMethodSpec s] 
{
    JMLNormalMethodSpec copy = (JMLNormalMethodSpec) s.copy();
    services.getImplementation2SpecMap().removeMethodSpec(copy);
}:
        normalspeccase[s] 
        ( 
            "also" normalspeccase[(JMLNormalMethodSpec) copy.copy()] 
        )*
;

exceptionalspecbody[JMLExceptionalMethodSpec s] :
        exceptionalspecclause[s] (exceptionalspecclause[s])*
    |
        LBRACE "|" exceptionalspeccaseseq[s] "|" RBRACE
    ;

exceptionalspeccaseseq[JMLExceptionalMethodSpec s] 
{
    JMLExceptionalMethodSpec copy = (JMLExceptionalMethodSpec) s.copy();
    services.getImplementation2SpecMap().removeMethodSpec(copy);
}:
        exceptionalspeccase[s] 
        ( 
            "also" exceptionalspeccase[(JMLExceptionalMethodSpec) copy.copy()] 
        )*
;

normalspecclause[JMLMethodSpec s] :
        ensuresclause[s]
    |
        assignableclause[s]
    |
        divergesclause[s]
    |
        whenclause[s]
    |
        durationclause[s]
    |
        workingspaceclause[s]
    ;

simplespecbodyclause[JMLMethodSpec s] :
        normalspecclause[s]
    |
        signalsclause[s]
    |
        signalsonlyclause[s]
    ;

exceptionalspecclause[JMLMethodSpec s] :
        assignableclause[s]
    |
        signalsclause[s]
    |
        signalsonlyclause[s]
    |
        divergesclause[s]
    |
        whenclause[s]
    |
        durationclause[s]
    |
        workingspaceclause[s]
    ;

//not implemented
whenclause[JMLMethodSpec s] :
        whenkeyword dummy = predornot ";"
    ;

whenkeyword:
        "when" 
    | 
        "when_redundantly"
    ;


//not implemented
durationclause[JMLMethodSpec s] :
        durationkeyword dummy = predornot ";"
    ;

durationkeyword:
        "duration" 
    | 
        "duration_redundantly"
    ;

//not implemented
workingspaceclause[JMLMethodSpec s] :
        workingspacekeyword 
        (
            NOT_SPECIFIED
        |
            dummy = specexpression (IF dummy = predicate)?
        )
        ";"
    ;

workingspacekeyword:
        "working_space" 
    | 
        "working_space_redundantly"
    ;

divergesclause[JMLMethodSpec s]
{
    Term t=null;
}:
        divergeskeyword 
        {
            setPreMode(true);
        } 
        t=predornot 
        {
            s.addDiverges(t);
        }
        ";"
; 

divergeskeyword :
        "diverges"
    |
        "diverges_redundantly"
    ;

assignableclause[AssignableSpec s] 
{
    SetOfLocationDescriptor locs = null;
}:
        assignablekeyword {setPreMode(true);} locs = conditionalstorereflist[s] ";"
        {
            s.addAssignable(locs);
        }
;

assignablekeyword :
        "assignable"
    |
        "modifies"
    |
        "modifiable"
    | 
        "assignable_redundantly"
    |   
        "modifiable_redundantly"
    | 
        "modifies_redundantly"
;

conditionalstorereflist[AssignableSpec s] 
    returns [SetOfLocationDescriptor set = SetAsListOfLocationDescriptor.EMPTY_SET]
{
    LocationDescriptor loc=null;
} :
        loc=conditionalstoreref[s]
        {           
            if(loc != null){
                set = set.add(loc);
            }
        }
        (
            "," loc=conditionalstoreref[s]
            {
                if(loc != null){
                    set = set.add(loc);
                }
            }
        )* 
;

conditionalstoreref[AssignableSpec s] returns [LocationDescriptor loc=null]
{
	Term t;
    Term t1=null;
}:
		{
			quantifiedArrayGuard = tf.createJunctorTerm(Op.TRUE);
		}
        t=storeref[s] ("if" t1=predicate)? 
        {
        	if(t != null) {
        	    if (t.op() instanceof Location) {
          	    	loc = new BasicLocationDescriptor(quantifiedArrayGuard, t);	           
       	    	    } else {       	    	    	
       	    	        reportError(new KeYSemanticException("Invalid assignable clause. " +
       	    	            "Expected a location, but " + t + " denotes a " + t.op().getClass().getName(), 
       	    	            getFilename(), getLine(), getColumn()));
       	    	    }
        	}
        	quantifiedArrayGuard = null;
        }
;

// not implemented
storereflist :
        dummy=storeref[null] ("," dummy=storeref[null])*
;

storeref[AssignableSpec spec] returns [Term t=null]
{
    String s;
}:
        t = storerefexpression
    |
        s = storerefkeyword[spec]
    |
        INFORMAL_DESCRIPTION
;

storerefkeyword[AssignableSpec spec] returns [String s=null]:
        (
            NOTHING {s="nothing";}
        |
            EVERYTHING {
               s = "everything";
               spec.addAssignable(SetAsListOfLocationDescriptor.
                  EMPTY_SET.add(EverythingLocationDescriptor.INSTANCE));   
            }
            
        |
            NOT_SPECIFIED {s="not_specified";}
        |
            PRIVATEDATA {s="private_data";}
        )
        {
           if(spec != null){          
                spec.setAssignableMode(s);
            }
        }
;

storerefexpression returns [Term t=null]
{
    String s;
    KeYJavaType kjt = null;
}:
        s=storerefname 
        {
            if(s.equals("this")){
                if (staticMode){
                    throw new KeYSemanticException("this in static context", 
                        getLine(), getColumn(), getFilename());
                }
                t = getTermForVariable((ProgramVariable) prefix());
            }else{                
                t = lookupVar(new Name(s));
            }
            if(t == null){
                kjt = getJavaInfo().getTypeByClassName(s);
            }   
        }
        (
            t=storerefnamesuffix[t, kjt] 
        )*
    ;

storerefnamesuffix[Term localPrefix, KeYJavaType kjt] returns [Term t=null]
{
    String s;
    ArraySpecIndexBound aib = null;
}:
        (
            (DOT "this") => DOT "this"
            {
                t = getTermForVariable((ProgramVariable) prefix());
            }
        |
            DOT id:IDENT 
            {
                s = id.getText();
                if(localPrefix != null){
                    kjt = services.getTypeConverter().getKeYJavaType(
                        localPrefix);
                }
                if(kjt != null){
                    //%%RB I do not think  this is okay, visible contexts?
                    ProgramVariable v = (ProgramVariable) getJavaInfo().lookupVisibleAttribute(s, kjt);
                    if ( v == null){
                        JMLClassSpec cs = 
                            services.getImplementation2SpecMap().getSpecForClass(kjt);
                        if(cs != null){
                            try{
                                v = cs.lookupModelField(new Name(id.getText()));
                            }catch(AmbigiousModelElementException e){
                                throw new KeYSemanticException(
                                    "Ambigious Model Element name",
                                     getLine(), getColumn(), getFilename());
                            }
                        }
                    }
                    if ( v == null) {
                        throw new NotDeclException("Attribute ", s, 
                            getFilename(), getLine(), getColumn());
                    }
                    t = (v.isStatic() ? getTermForVariable(v) : df.dot(localPrefix, v));                    
                }
            }
        |
            "[" aib = specarrayrefexpr[localPrefix] "]"
            {
                if(aib != null && localPrefix != null){
                    Term indexTerm;
                    
                    if (aib.singleValue()) {
                    	indexTerm = aib.lower();
                    } else {
                    	if(quantifiedArrayGuard == null) {
                            throw new KeYSemanticException(
                                "Quantified array expressions are "
                                + "only allowed in locations.", 
                                getLine(), 
                                getColumn(), 
                                getFilename());
                    	}
                    	final LogicVariable indexVar = 
                        new LogicVariable(
                            new Name("i"), (Sort) sorts().lookup(new Name("int")));
                        indexTerm = df.var(indexVar);
                        if (aib.isStar()) {
                            quantifiedArrayGuard = df.and(quantifiedArrayGuard, df.tt());
                        } else {
                            Term fromTerm = df.leq(aib.lower(), indexTerm, getServices());
                            Term toTerm = df.leq(indexTerm, aib.upper(), getServices());
                            Term guardTerm = df.and(fromTerm, toTerm);
                            quantifiedArrayGuard = df.and(quantifiedArrayGuard, guardTerm);						   
                        } 
                    }
                    t = df.array(localPrefix, indexTerm);
                 }
             }
            )
    ;

specarrayrefexpr[Term prefix] returns [ArraySpecIndexBound aib = new ArraySpecIndexBound()] 
{
    Term t;
}:
        (
            t=specexpression { aib.setLower(t); }
            (
                DOTDOT t = specexpression 
                {
                     aib.setUpper(t); 
                }
            )?
        )
    |
        MULT 
        {
            aib.setStar(true);
        }
    ;

storerefname returns [String s=null] :
        id:IDENT {s=id.getText();}
    |   
        "this" 
        {
            s = "this";
        }
    |
        "super"
        {
            s = "super";
        }
;

signalsonlyclause[JMLMethodSpec s]
{
    KeYJavaType exc=getReferenceType("Exception");
    KeYJavaType only = null;
    Term t = df.ff();
    Term instof = null;
    ProgramVariable v = new LocationVariable(new ProgramElementName("e"), exc);
    Term vTerm = df.var(v);
}:
        "signals_only" {setPreMode(false);} 
        {
                bindProgVars(v);
        }
        (
            only = referencetype (",")?
            {
                SortDefiningSymbols os = (SortDefiningSymbols)(only.getSort());
                InstanceofSymbol func
                    = (InstanceofSymbol)os.lookupSymbol(InstanceofSymbol.NAME);
                instof = df.equals(df.func(func, vTerm), BOOL_TRUE);
                t = df.or(t, instof);
            }
        )+ 
        ";"
        {
            s.addSignals(exc, v, t);
            unbindProgVars();
        }
; exception
        catch [RuntimeException th] {
            unbindProgVars();
            throw th;
        }   
   

signalsclause[JMLMethodSpec s]{
    KeYJavaType exc=null;
    Term t = df.tt();
    ProgramVariable v = null;
    boolean bound = false;
}:
        signalskeyword {setPreMode(false);} 
        "(" exc = referencetype 
        (id:IDENT 
            {
                v = new LocationVariable(
                    new ProgramElementName(id.getText()), exc);
                bindProgVars(v);
                bound = true;
            }
        )? 
        ")" (t=predornot)? ";"
        {
            if(t != null){
                s.addSignals(exc, v, t);
            }
            if(v != null){
                unbindProgVars();
            }
        }
; exception
        catch [RuntimeException th] {
        if (bound) unbindProgVars();
        throw th;
        }   


signalskeyword:
        (   
            "signals"
        |
            "exsures"
        |
            "signals_redundantly"
        |
            "exsures_redundantly"
        )
;

requiresclause[JMLMethodSpec s] 
{
    Term t=null; 
}:
        requireskeyword {setPreMode(true);} t=predornot 
        {
            if(t!=null) s.addPre(t); 
        } 
        ";"
    ;

requireskeyword :
        (
            "requires"
        |
            "pre"
        |
            "requires_redundantly"
        |
            "pre_redundantly"
        )
    ;

ensuresclause[JMLMethodSpec s] 
{
    Term t=null; 
}:
        ensureskeyword {setPreMode(false);} t=predornot 
        {
            if(t!=null) s.addPost(t); 
        } 
        ";"
    ;

ensureskeyword :
        (
            "ensures"
        |
            "post"
        |
            "ensures_redundantly"
        |
            "post_redundantly"
        )
    ;

predornot returns [Term t=null]:
        t = predicate 
    |
        NOT_SPECIFIED
    ;

predicate returns [Term t=null]:
        t = specexpression
    ;

specexpression returns [Term t=null]:
        t = expression
    ;

spec_expression_list :
        dummy = specexpression ("," dummy = specexpression)*
    ;

expression returns [Term t=null]:
        t=assignmentexpr
    ;

assignmentexpr returns [Term t=null]:
        t=conditionalexpr
    ;

conditionalexpr returns [Term t=null]
{
    Term t1,t2;
}:
        t=equivalenceexpr 
        (
            "?" t1=conditionalexpr ":" t2=conditionalexpr
            {
                t = tf.createIfThenElseTerm(t, t1, t2);
            }
        )?
    ;

equivalenceexpr returns [Term t=null]
{
    Term a=null;
}:
        t=impliesexpr 
        (
            EQV a=equivalenceexpr 
            {
                t = df.equiv(t,a);
            }
        |
            ANTIV a=equivalenceexpr 
            {              
                t = df.not(df.equiv(t, a));
            }
        )?
    ;
        
impliesexpr returns [Term t=null]
{
    Term a=null;
}:
        t=logicalorexpr 
        (
            "==>" a=impliesnonbackwardexpr
            { 
                t = df.imp(t,a);
            }
        |
            (
                "<==" a=logicalorexpr
                { 
                    t = df.imp(a,t);
                }
            )+
        )?
;

impliesnonbackwardexpr returns [Term t=null]
{
    Term a=null;
}:
        t=logicalorexpr ("==>" a=impliesnonbackwardexpr
            { t = df.imp(t,a); })?
;        

logicalorexpr returns [Term t=null]
{
    Term a=null;
}:
        t=logicalandexpr ("||" a=logicalorexpr {t = df.or(t, a);})?
;

logicalandexpr returns [Term t=null]
{
    Term a=null;
}:
        t=inclusiveorexpr ("&&" a=logicalandexpr
            {t = df.and(t, a);})?
;

inclusiveorexpr returns [Term t=null]
{
    Term a=null;
}:
        t=exclusiveorexpr 
        (
            "|" a=inclusiveorexpr
            {
                if(t.sort() == Sort.FORMULA && a.sort() == Sort.FORMULA){
                    t = df.or(t, a);
                }else if(t.sort().equals(a.sort())){                   
                    t = df.func(aOP.getOr(isLong(t) || isLong(a)), new Term[]{t,a});
                }else{
                    throw new antlr.SemanticException(
                        "Bitwise-Or not valid with subterms "+t+" and "+a);
                }
            }
        )?
;

exclusiveorexpr returns [Term t=null]
{
    Term a;
}:
        t=andexpr 
        (XOR a=exclusiveorexpr 
            {
                if(t.sort() == Sort.FORMULA && a.sort() == Sort.FORMULA){   
                    final Term nt = df.not(t);
                    t = df.or(df.and(nt, df.not(a)), df.and(nt, a));
                }else if(t.sort().equals(a.sort())){                    
                    t = df.func(aOP.getXor(isLong(t) || isLong(a)), new Term[]{t,a});
                }else{
                    throw new antlr.SemanticException(
                        "Bitwise-Xor not valid with subterms "+t+" and "+a);
                }
            }
        )?
;

andexpr returns [Term t=null]
{
    Term a=null;
}:
        t=equalityexpr
        (
            "&" a=andexpr
            {
                if(t.sort() == Sort.FORMULA && a.sort() == Sort.FORMULA){
                    t = df.and(t,a);
                }else if(t.sort().extendsTrans(a.sort()) || 
                         a.sort().extendsTrans(t.sort())){
                    t = df.func(aOP.getAnd(isLong(t) || isLong(a)), new Term[]{t,a});
                }else{
                    throw new antlr.SemanticException(
                        "Bitwise-And not valid with subterms "+t+" and "+a);
                }
            }
        )?
;

equalityexpr returns [Term t=null]
{
    Term a1;
}:
        t=relationalexpr 
        (
            "==" a1=equalityexpr { t = tf.createEqualityTerm(t, a1);}
        |
            "!=" a1=equalityexpr 
            {               
                t  = df.not(tf.createEqualityTerm(t, a1));
            }
        )?
;

relationalexpr returns [Term t=null]
{
    Term a1;
    Function f;
    KeYJavaType type;
}:
        t=shiftexpr
        (
            LT a1=shiftexpr 
            {
                f = (Function) functions().lookup(new Name("lt"));
                t = tf.createFunctionTerm(f, t, a1);
            }
        |
            GT a1=shiftexpr
            {
                f = (Function) functions().lookup(new Name("gt"));
                t = df.func(f, t, a1);
            }
        |
            LEQ a1=shiftexpr
            {
                f = (Function) functions().lookup(new Name("leq"));
                t = df.func(f, t, a1);
            }
        |
            GEQ a1=shiftexpr
            {
                f = (Function) functions().lookup(new Name("geq"));
                t = df.func(f, t, a1);
            }
        |
            "instanceof" type=typespec 
            {
                SortDefiningSymbols s = (SortDefiningSymbols)(type.getSort());
                InstanceofSymbol func
                    = (InstanceofSymbol)s.lookupSymbol(InstanceofSymbol.NAME);
                final Term object = t;
                t = df.and(df.equals(df.func(func, t), BOOL_TRUE), 
                           df.not(df.equals(object, df.NULL(services))));
            }
        |
            ST a1 = shiftexpr
            {
                throw new NotSupportedExpressionException("<:");
            }
            
        )?
;

shiftexpr returns [Term t=null]
{
    Term a=null;
}:
        t=additiveexpr
        (
            ">>" a=additiveexpr 
            {
                Function f = aOP.getShiftRight(isLong(t));
                t = df.func(f, t, a);
            }
        |   
            "<<" a=additiveexpr 
            {
                Function f = aOP.getShiftLeft(isLong(t));
                t = df.func(f, t, a);
            }
        |   
            ">>>" a=additiveexpr 
            {
                Function f = aOP.getUnsignedShiftRight(isLong(t));
                t = df.func(f, t, a);
            }
        )*
;

additiveexpr returns [Term t=null]
{
    Term a1;
    Function f;
}:
        t=multexpr
        (
            "+" a1=multexpr
            {
                f = aOP.getAdd(isLong(t) || isLong(a1));
                t = df.func(f, t, a1);
            }
        |
            "-" a1=multexpr
            {
                f = aOP.getSub(isLong(t) || isLong(a1));
                t = df.func(f, t, a1);
            }
        )*
;

multexpr returns [Term t=null]
{
    Term a1;
    Function f;
}:
        t=unaryexpr
        (
            MULT a1=unaryexpr
            {  
                f = aOP.getMul(isLong(t) || isLong(a1));
                t = df.func(f, t, a1);
            }
        |
            DIV a1=unaryexpr
            { 
                f = aOP.getDiv(isLong(t) || isLong(a1));
                t = df.func(f, t, a1);
            }
        |
            "%" a1=unaryexpr
            { 
                f = aOP.getMod(isLong(t) || isLong(a1));
                t = df.func(f, t, a1);
            }
        )*
;

unaryexpr returns [Term t=null]{
    Function neg;
    KeYJavaType type;
}:
        "+" t=unaryexpr
    |
        "-" t=unaryexpr 
        {
            neg = aOP.getMinus(isLong(t));
            t = tf.createFunctionTerm(neg,new Term[]{t});
        }
    |
        ("(" builtintype ")") =>
        "(" type=builtintype ")" t=unaryexpr
        {
            if(PrimitiveType.JAVA_BYTE.equals(type.getJavaType())){
                if(aOP.getCastToByte() != null){	 
                    t = tf.createFunctionTerm(aOP.getCastToByte(),t);	 
                }	 
            }else if(PrimitiveType.JAVA_SHORT.equals(type.getJavaType())){	 
                if(aOP.getCastToShort() != null){	 
                        t = tf.createFunctionTerm(aOP.getCastToShort(),t);	 
                }	 
            }else if(PrimitiveType.JAVA_INT.equals(type.getJavaType())){	 
                if(aOP.getCastToInt() != null){	 
                    t = tf.createFunctionTerm(aOP.getCastToInt(),t);	 
                }	 
            }else if(PrimitiveType.JAVA_LONG.equals(type.getJavaType())){	 
                if(aOP.getCastToLong() != null){	 
                    t = tf.createFunctionTerm(aOP.getCastToLong(),t);	 
                }	 
            }
        }
    |
        ("(" referencetype ")" ) => 
           "(" type=referencetype ")" t=unaryexpr
        {
           t = tf.createCastTerm((AbstractSort)type.getSort(),t);
        }
    |
        t = unaryexprnotplusminus
;

unaryexprnotplusminus returns [Term t=null]:
        "!" t=unaryexpr {t = df.not(t);}
    |
        "~" t=unaryexpr 
        { 
            Function f = aOP.getNeg(isLong(t));
            t = tf.createFunctionTerm(f,new Term[]{t});
        }
    |
        t=postfixexpr
;

postfixexpr returns [Term t=null]
{
    tempkjt = translator.getCLDKeYJavaType();
}:
        t = primaryexpr (t = primarysuffix[tempkjt, t])*
        {
            if(t == null){
                throw new NotDeclException("variable or method ",
                    packageName, getFilename(), getLine(), getColumn());
            }
        }
;

primaryexpr returns [Term t=null]
{
    KeYJavaType kjt = null;
    ProgramVariable v = null;
}:
        t=constant
    |   id:IDENT 
        {   
            tempkjt = translator.getCLDKeYJavaType();
            if(LA(1)==LPAREN){
                methodname = id.getText();
                return null;
            }           
            t = lookupVar(new Name(id.getText()));           
            if(t == null) {
                try {
                    kjt = getJavaInfo().getTypeByClassName(id.getText());
                } catch(RuntimeException e){}
                if(kjt == null){
                    packageName = id.getText();
                }else{
                    packageName = "";
                }
            } else {            	
                if(t.op() instanceof ProgramVariable){
                    kjt = ((ProgramVariable) t.op()).getKeYJavaType();                    
                }else if (t.op() instanceof AttributeOp){
                    kjt = (((AttributeOp) t.op()).attribute()).getKeYJavaType();                    
                }else if(t.op() instanceof LogicVariable){
                    kjt = getJavaInfo().getKeYJavaType(t.sort());
                }
                if(PrimitiveType.JAVA_BOOLEAN.equals(kjt.getJavaType())){
                    t = df.equals(t, BOOL_TRUE);
                }
            }
            tempkjt = kjt;
        }
    |   "true"  { t = df.tt(); }
    |   "false" { t = df.ff(); }
    |   "null"  { t = df.NULL(services);} 
    |   t = jmlprimary 
    |   "this" 
        {
            t = df.var((ProgramVariable) prefix());
            tempkjt = ((ProgramVariable) prefix()).getKeYJavaType();
        }
    |   t = new_expr
;

primarysuffix[KeYJavaType kjt, Term t] returns [Term result = null]{
    ListOfTerm l=SLListOfTerm.EMPTY_LIST;
    Term arg = null; 
    String mName = methodname;
    methodname = null;
}:
        (DOT id:IDENT
            {
                if(LA(1)==LPAREN){
                    methodname = id.getText();
                    packageName = "";
                    return t;
                }
                if(t != null && t.sort() instanceof ObjectSort){
                    kjt = getJavaInfo().getKeYJavaType(t.sort());
                }
                ProgramVariable v = null;
                if(kjt != null){
                    v = (ProgramVariable) getJavaInfo().
                            lookupVisibleAttribute(id.getText(), kjt);
                }
                if(v==null && kjt != null){
                    JMLClassSpec cs = services.getImplementation2SpecMap().getSpecForClass(kjt);
                    if(cs != null){
                        try {
                            v = cs.lookupModelField(new Name(id.getText()));
                        } catch(AmbigiousModelElementException e){
                            throw new KeYSemanticException(
                                "Ambigious Model Element name",
                                 getLine(), getColumn(), getFilename());
                        }
                    }
                }
                if ( v == null /*&& !("length").equals(id.getText())*/ ) {
                    KeYJavaType classType = null;
                    try {
                        classType = getJavaInfo().getTypeByClassName(
                            packageName + "." + id.getText());
                    } catch(RuntimeException e) {}
                    if(classType == null){
                        packageName += "."+id.getText();
                    }else{
                        packageName = "";
                        this.tempkjt = classType;
                    }
                }else{
                    if (v.isStatic()) {
                        result = df.var(v);
                    } else {
                        result = df.dot(t, v);
                    }
                    this.tempkjt = v.getKeYJavaType();
                    if (PrimitiveType.JAVA_BOOLEAN.equals(this.tempkjt.getJavaType())){
                        result = df.equals(result, BOOL_TRUE);
                    }
                }
            }
        )
    |
        "(" (l=expressionlist)? ")" 
        {
            ListOfKeYJavaType sig = getTypeList(l);
            
            if (t != null && t.sort() instanceof ObjectSort){
                kjt = getJavaInfo().getKeYJavaType(t.sort());
            } 
            
            ProgramMethod pm = getJavaInfo().getProgramMethod(kjt, mName, 
                sig, translator.getCLDKeYJavaType());
            // maybe it's a model method
            if(pm == null){
                JMLClassSpec cs = 
                    services.getImplementation2SpecMap().getSpecForClass(kjt);
                if(cs != null){
                    try{
                        pm = cs.lookupModelMethod(
                            new Name(kjt.getSort()+ "::" + mName));
                        if(pm == null){
                            pm = cs.lookupModelMethod(new Name(mName));
                        }
                        
                    }catch(AmbigiousModelElementException e){
                        System.err.println(e.toString());
                    }
                }
            }
            if(pm == null){
                throw new NotDeclException("method", 
                    mName, getFilename(), getLine(), getColumn(), "in type "+kjt);
            }   
            if(!pm.isStatic() && staticMode && (t==null || t.op().equals(prefix()))){
                throw new KeYSemanticException("Call to instance method "+
                    "in static context", 
                    getLine(), getColumn(), getFilename());
            }
            Term[] sub;
            int i=0;
            if(pm.isStatic()){
                sub = new Term[sig.size()];
            }else{
                sub = new Term[sig.size()+1];
                if(t==null){
                    sub[i++] = df.var((ProgramVariable) prefix());
                }else{
                    sub[i++] = t;
                }
            }
            final IteratorOfTerm it = l.iterator();            
            while (it.hasNext()) {
                Term temp = simplifyArgument(it.next());
                if (temp.sort() == Sort.FORMULA){
                    final Term var = 
                    	df.var(new LocationVariable(new ProgramElementName("jml_p" +(paramVarCount++)),
                               getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN)));
                    sub[i++] = createModelMethod("formula"+(mmCount++), var, null, 
                                                 df.equiv(temp, df.equals(var, BOOL_TRUE)));
                } else {
                    sub[i++] = temp;
                }
            }
            result = df.func(pm, sub);
            if (PrimitiveType.JAVA_BOOLEAN.equals(pm.getKeYJavaType().getJavaType())){
                result = df.equals(result, BOOL_TRUE);
            }
            this.tempkjt = pm.getKeYJavaType();
        }
    |
        "["arg = expression "]"
        {
            result = df.array(t, arg);
            this.tempkjt = services.getTypeConverter().getKeYJavaType(result);
            if (PrimitiveType.JAVA_BOOLEAN.equals(tempkjt.getJavaType())) {
                result = df.equals(result, BOOL_TRUE);
            }
        }
;

new_expr returns [Term t=null]
{
    KeYJavaType kjt;
    ListOfTerm l;
}:
        "new" kjt=type l = new_suffix
        {
            final ListOfKeYJavaType sig = getTypeList(l);
            final Constructor c = 
            	getJavaInfo().getKeYProgModelInfo().getConstructor(kjt, sig);
            if (!(c instanceof ConstructorDeclaration)) {
                throw new NotSupportedExpressionException("Default Constructor");
            }            
            ProgramMethod cm = 
                new ProgramMethod((ConstructorDeclaration) c, kjt, 
                                   translator.getCLDKeYJavaType(), PositionInfo.UNDEFINED);
            
            int i=0;
            final Term[] sub = new Term[sig.size()];
            final IteratorOfTerm it = l.iterator();
            while ( it.hasNext() ) {
                final Term temp = simplifyArgument(it.next());
                if(temp.sort() == Sort.FORMULA){
                    final Term var = df.var(new LocationVariable(
                        new ProgramElementName("_param"+(paramVarCount++)),
                        getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN)));
                    sub[i] = createModelMethod("formula"+(mmCount++), var, 
                                               null, 
                                               df.equiv(temp, df.equals(var, BOOL_TRUE)));                    
                } else {
                    sub[i] = temp;
                }
                i++;
            }
            t = df.func(cm, sub);
            if (PrimitiveType.JAVA_BOOLEAN.equals(cm.getKeYJavaType().getJavaType())){
                t = df.equals(t, BOOL_TRUE);
            }
            this.tempkjt = kjt;            
        }
    ;

new_suffix returns [ListOfTerm l = SLListOfTerm.EMPTY_LIST]:
        "(" ( l=expressionlist )? ")" 
    ;

expressionlist returns [ListOfTerm l = SLListOfTerm.EMPTY_LIST]
{
    Term t;
}:
        t = expression {l=l.append(t);} ("," t=expression {l=l.append(t);})* 
;

constant returns [Term t=null]:
        t=javaliteral
;

javaliteral returns [Term t=null]:
        t=integerliteral
    |
        STRING_LITERAL 
        {
            throw new NotSupportedExpressionException("String literal");
        }
    |
        CHAR_LITERAL 
        {
            throw new NotSupportedExpressionException("Char literal");
        }
    ;

integerliteral returns [Term t=null]:
        t=decimalintegerliteral
;

decimalintegerliteral returns [Term t=null]:
        t=decimalnumeral
;

decimalnumeral returns [Term t=null]:
        n:DIGITS {t = toZNotation(n.getText());}
;

jmlprimary returns [Term t=null]
{
    KeYJavaType dummykjt;
}:
        RESULT 
        {
            t = df.var((ProgramVariable) result);
            if (PrimitiveType.JAVA_BOOLEAN.equals(result.getKeYJavaType().getJavaType())){
                t = df.equals(t, BOOL_TRUE);
            }
            tempkjt = result.getKeYJavaType();
        }
    |
        ("(" QUANTIFIER) => t=specquantifiedexpression
    |
        OLD { inOld = true; } "(" t=specexpression ")" 
        {
	    if (isOldAllowed) {
	        t = getOld(t);
            } else {
		throw new KeYSemanticException("JML construct "+
                  "\\old not allowed in this context,"+
                  "e.g. in loop invariants",
                  getFilename(), getLine(), getColumn());
            }
            inOld = false;  
        }
    |   CREATED "(" t = specexpression ")"
       {    
   	   if (!(t.sort() instanceof ObjectSort)) {
   	   	throw new KeYSemanticException("\\created can only be applied on objects.");
   	   }
   	   ProgramVariable created = services.getJavaInfo().
   	   	getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED,
   	   	services.getJavaInfo().getJavaLangObject());
       	   t = df.equals(df.dot(t, created), df.TRUE(services));
       }
    |
        NONNULLELEMENTS "(" t=specexpression ")"
        {
            t = nonNullElements(t);
        }
    |   INFORMAL_DESCRIPTION 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "informal description");
        }
    |   NOT_MODIFIED "(" storereflist ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\not_modified");
        }
    |   FRESH "(" spec_expression_list ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\fresh");
        }
    |   REACH "(" dummy = specexpression ")"
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\reach");
        }
    |   DURATION "(" dummy = expression ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\duration");
        }
    |   SPACE "(" dummy = specexpression ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\space");
        }
    |   WORKINGSPACE "(" dummy = expression ")"
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\working_space");
        }
//    |   QUANTIFIER "(" dummy = expression ")"
    |   TYPEOF "(" dummy = specexpression ")"
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\typeof");
        }
    |   ELEMTYPE "(" dummy = specexpression ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\elemtype");
        }
    |   TYPE_SMALL "(" dummykjt = type ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\type");
        }
    |   LOCKSET
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\lockset");
        }
    |   IS_INITIALIZED "(" dummykjt=referencetype ")" 
        {
            ProgramVariable ci = 
	            services.getJavaInfo().getAttribute
	                (ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, dummykjt);
            t = df.equals(df.var(ci), BOOL_TRUE);
        }
    |   INVARIANT_FOR "(" dummy=specexpression ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\invariant_for");
        }
    |   ( "(" LBLNEG ) => "(" LBLNEG IDENT dummy=specexpression ")"
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\lblneg");
        }
    |   ( "(" LBLPOS ) => "(" LBLPOS IDENT dummy=specexpression ")" 
        {
            throw new NotSupportedExpressionException("JML construct "+
                "\\lblpos");
        }
    |
        NOWARN
        {
            throw new NotSupportedExpressionException("\\nowarn", true);
        } 
    |   
        "(" t=expression ")"

;

specquantifiedexpression returns [Term t=null]
{
    Term a=null; 
    ListOfNamed decls=null;
}:
        "("
        q:QUANTIFIER decls=quantifiedvardecls {bindVars(decls);} ";" 
        (
            ((predicate)? ";" ) => (a=predicate)? ";" t=specexpression
        |
            (";")? t=specexpression 
        )
        {
            t = buildQuantifierTerm(q.getText(), decls, a, t); 
            unbindVars(); 
        }
        ")"
;
exception
        catch [NotSupportedExpressionException ex] {
        unbindVars();
        throw ex;
        }   

quantifiedvardecls returns [ListOfNamed decls=SLListOfNamed.EMPTY_LIST]
{
    KeYJavaType kjt = null;
    LogicVariable v = null;
}:
        kjt = typespec v = quantifiedvariabledeclarator[kjt] 
        { decls=decls.append(v); }
        ("," v = quantifiedvariabledeclarator[kjt] { decls=decls.append(v); })*
;

typespec returns [KeYJavaType kjt = null]{
    int dim = 0;
}:
        kjt=type 
        (dim = dims 
            {   
                if(dim != 0){
                    kjt = getArrayTypeAndEnsureExistence(kjt.getSort(), dim);
                }
            }
        )?
;

dims returns [int dim = 0]:
        ("[" "]" {dim++;} )+
    ;

type returns [KeYJavaType kjt = null]:
        (builtintype) => kjt = builtintype
    |
        kjt = referencetype
    |
        // \TYPE not supported
        TYPE
        {
            kjt = getJavaInfo().getJavaLangObject();    
        }
;

referencetype returns [KeYJavaType kjt = null]
{
    String n = null;
}:
        n=name 
        {
            kjt = getReferenceType(n);
        }
;   

builtintype returns [KeYJavaType kjt = null]
{
    String type = null;    
}:
        (
            "byte" {type = "byte";}
        |
            "short" {type = "short";}
        |
            "int" {type = "int";}
        |
            "long" {type = "long";}
        |
            "boolean" {type = "boolean";}
        |
            "void" {type = "void";}
        |
            //no support for bigint yet
            BIGINT {type = "long";}
        |
            REAL
            {
                throw new NotSupportedExpressionException("Type real");
            }
        )
        {
            kjt = getJavaInfo().getKeYJavaType(type);
            if (kjt == null) {
                throw new NotDeclException("type", type, getFilename(), getLine(), getColumn());
            }
        }
;

name returns [String s = null]:
        id:IDENT {s=id.getText();} (DOT id2:IDENT {s+="."+id2.getText();})*
;

quantifiedvariabledeclarator[KeYJavaType kjt] returns [LogicVariable v=null]
{
    int dim = 0;
}:
   id:IDENT (dim=dims)?           
   {
       if (dim != 0) {
          kjt = getArrayTypeAndEnsureExistence(kjt.getSort(), dim);
          final JavaInfo javaInfo = services.getJavaInfo();
       }
       v = new LogicVariable(new ProgramElementName(id.getText()), kjt.getSort());
   }
;
