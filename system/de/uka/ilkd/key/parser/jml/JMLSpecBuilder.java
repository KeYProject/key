// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser.jml;

import java.io.StringReader;
import java.util.*;

import antlr.RecognitionException;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.IteratorOfProgramElement;
import de.uka.ilkd.key.java.ListOfProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.recoderext.ClassInitializeMethodBuilder;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.jml.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IteratorOfProgramMethod;
import de.uka.ilkd.key.logic.op.ListOfProgramMethod;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.util.ExceptionHandlerException;

/** 
 * provides methods for parsing the specifications of a single class/interface.
 */
public class JMLSpecBuilder {
    
    private TypeDeclaration cd; 
    private Services services; 
    private NamespaceSet nss; 
    private TermBuilder tb;
    private boolean parsedMethods = false; 
    private boolean parsedClass = false;
    private LinkedHashMap method2specs = new LinkedHashMap();
    private LinkedHashMap method2term = null;
    private JMLClassSpec classSpec = null;
    private ArithOpProvider aOP = null;
    //contains jml-comments in cd
    private LinkedHashSet jmlComments = null;
    //contains jml-comments without model method declarations.
    private LinkedHashSet jmlCommentsWithoutMM = null;
    //contains jml-comments without model method  and model field declarations.
    private LinkedHashSet jmlCommentsWithoutMFMM = null;
    //where the sources for the input are below
    private String javaPath;
   
    public JMLSpecBuilder(TypeDeclaration cd, Services services, 
			  NamespaceSet nss, TermBuilder tb, String javaPath, 
                          boolean javaSemantics){
	this.cd = cd;
	this.services = services;
	this.nss = nss;
	this.tb = tb;      
	aOP = new DefaultArithOpProvider(nss.functions(), javaSemantics);
	Comment[] comments = cd.getComments();
	if(comments != null){
	    jmlComments = new LinkedHashSet();
	    for(int i=0; i<comments.length; i++){
		if(comments[i].containsJMLSpec()){
		    jmlComments.add(comments[i].getJMLSpec());
		}
	    }
	}
	this.javaPath=javaPath;
    }

    public TypeDeclaration getTypeDeclaration(){
        return cd;
    }

    /**
     * returns a term containing the proofobligations for the methodspecs
     * of <code>pm</code> and the invariant and constraint proofobligation
     * for the containing class. 
     */
    public Term buildProofObligation(ProgramMethod pm){
	Implementation2SpecMap ism = services.getImplementation2SpecMap();
	SetOfJMLMethodSpec specs = ism.getSpecsForMethod(pm);
	classSpec = ism.getSpecForClass(pm.getContainerType());
	return makeConjunction(specs, pm);
    }

    /** 
     * parses jml model fields declared in <code>cd</code>. 
     * Can't be called before parseModelMethodDecls() has been called
     */
    public void parseModelFieldDecls() throws ProofInputException {
	if(jmlCommentsWithoutMFMM == null && jmlCommentsWithoutMM != null){
	    jmlCommentsWithoutMFMM = new LinkedHashSet();
	    Iterator it = jmlCommentsWithoutMM.iterator();
	    while(it.hasNext()){
		String s = (String) it.next();
		parseFieldDecl(s, jmlCommentsWithoutMFMM, classSpec);
	    }
	}else{
	    throw new ProofInputException(jmlCommentsWithoutMFMM == null?
					  "Tried to parse model field "+
					  "declarations before parsing "+
					  "model method declarations":
					  "already parsed model field "+
					  "declarations for class/interface "+
					  cd);
	}
    } 

    /** 
     * parses jml model methods declared in <code>cd</code>. 
     */
    public void parseModelMethodDecls() throws ProofInputException {
	if(jmlCommentsWithoutMM == null){
	    classSpec = new JMLClassSpec(services, cd, nss, javaPath);
	    jmlCommentsWithoutMM = new LinkedHashSet();
	    Iterator it = jmlComments.iterator();
	    while(it.hasNext()){
		String s = (String) it.next();
		parseMethodDecl(s, jmlCommentsWithoutMM, classSpec);
	    }
	}else{
	    throw new ProofInputException("already parsed model method "+
					  "declarations for class/interface "+
					  cd);
	}
    } 

    /**
     * parses jml specification like invariants, constraints or represents
     * in <code>cd</code>. parseModelMethodDecls() and parseModelFieldDecls()
     * have to be called first.
     */
    public void parseJMLClassSpec() throws ProofInputException {
	if(!parsedClass && jmlCommentsWithoutMFMM != null){
	    Iterator it = jmlCommentsWithoutMFMM.iterator();
	    while(it.hasNext()){
		String s = (String) it.next();
		if(s.trim().equals("") || s.matches("@?\\s*in \\w+;")) continue;
		StringReader stream = new StringReader(s);
		KeYJMLParser parser = 
		    new KeYJMLParser(new KeYJMLLexer(stream),
				     "no file, parsing comment from "+
				     cd.getName(), services, nss,
				     TermFactory.DEFAULT, cd, 
				     null, classSpec, aOP, javaPath);
		try{
		    parser.parseClassSpec();
		} catch(ExceptionHandlerException e1){
		    if(!(e1.getCause() instanceof 
			 NotSupportedExpressionException)){
			if (e1.getCause() instanceof RecognitionException) {
                            reportRecognitionException((RecognitionException) e1.getCause());                     
                        } else {                        
                            throw e1;
                        }
		    }else{
			services.getExceptionHandler().clear();
		    }
		} catch (antlr.RecognitionException e) {                   
                    reportRecognitionException(e);
                }catch (antlr.ANTLRException e) {                   
		    throw new ProofInputException(e);
		}
	    }
	    parsedClass = true;
	}else{
	    if(jmlCommentsWithoutMFMM == null){
		throw new ProofInputException("tried to parse class spec "+
					      "without parsing model "+
					      "declarations for class "+
					      cd+" first");
	    }
	}
    }

    /**
     * @param e1
     * @throws ProofInputException
     */
    private void reportRecognitionException(RecognitionException e) 
    throws ProofInputException {   
        int line = e.getLine();
        int column = e.getColumn();
        throw 
          new ProofInputException(e.getFilename()+
                  "("+line+","+column+"): "+e.getMessage());
    }

    public NamespaceSet namespaces(){
	return nss;
    }

    private void parseMethodDecl (String s, Set otherSpecs, JMLClassSpec cs) 
	throws ProofInputException{
	int mIndex = s.indexOf("model ");
	if(mIndex == -1 || (s.indexOf("_behavior") == -1 &&
	   s.indexOf("requires") == -1)){
	    otherSpecs.add(s);
	    return;
	}
	int start = s.substring(0, mIndex+1).lastIndexOf("\n") + 1;
	int end = s.indexOf(";", mIndex);
	int lbIndex = s.indexOf("{", mIndex);
	if(end == -1 || (end > lbIndex && lbIndex != -1)){
	    end = s.length()-1;
	}
	int pIndex = s.indexOf("(", mIndex);
	if(pIndex > end || pIndex == -1){
	    if(end == s.length()-1 || pIndex == -1){
		otherSpecs.add(s);
	    }else{
		otherSpecs.add(s.substring(0,end));
		parseMethodDecl(s.substring(end+1), otherSpecs, cs);
	    }
	    return;
	}
	String methDecl = s.substring(start, end+1);
	StringReader stream = new StringReader(methDecl);
	String nonMethSpec;
	if(s.indexOf("_behavior") != -1){
	    nonMethSpec = 
		s.substring(0,start).split("public +[a-z]+_behavior" , 2)[0];
	}else{
	    nonMethSpec = 
		s.substring(0,start).split("requires" , 2)[0];
	}
	String methSpec = 
	    "/*@ "+s.substring(0,start).substring(nonMethSpec.length())+" @*/";
	otherSpecs.add(nonMethSpec);

	KeYJMLParser parser = 
	    new KeYJMLParser(new KeYJMLLexer(stream),
			     "parsing comment from "+
			     cd.getName(),
			     services, nss,
			     TermFactory.DEFAULT, cd, 
			     null, cs, aOP, javaPath);
	try{
	    parser.parseMethodDecl(methSpec);
	}catch(ExceptionHandlerException e1){
	    if(!(e1.getCause() instanceof 
		 NotSupportedExpressionException)){
		if (e1.getCause() instanceof RecognitionException) {
		    reportRecognitionException((RecognitionException) e1.getCause());
                } else {
                    throw e1;
                }
	    }else{
		services.getExceptionHandler().clear();
	    }
	} catch (RecognitionException e) {
            reportRecognitionException(e);
        } catch (antlr.ANTLRException e) {
	    throw new ProofInputException(e);
	}
	parseMethodDecl(s.substring(end+1), otherSpecs, cs);
    }

    private void parseFieldDecl (String s, Set otherSpecs, JMLClassSpec cs) 
	throws ProofInputException{
	
	int mIndex = s.indexOf("model ");
	if(mIndex == -1) mIndex = s.indexOf("ghost");
	if(mIndex != -1){
	    int start = s.substring(0, mIndex+1).lastIndexOf("\n");
	    int end = s.indexOf(";", mIndex);
	    int endNextLine = s.indexOf(";", end+1);
	    if(s.indexOf("in", end) != -1 && 
	       s.indexOf("in", end) < endNextLine){
		end = endNextLine;
	    }
	    otherSpecs.add(s.substring(0, start+1));
	    StringReader stream = 
		new StringReader(s.substring(start+1, end+1));
	    KeYJMLParser parser = 
		new KeYJMLParser(new KeYJMLLexer(stream),
				 "parsing comment from "+
				 cd.getName(),
				 services, nss,
				 TermFactory.DEFAULT, cd, 
				 null, cs, aOP, javaPath);
	    try{
		parser.parseFieldDecl();

	    }catch(ExceptionHandlerException e1){
		if(!(e1.getCause() instanceof 
		     NotSupportedExpressionException)){
		    if (e1.getCause() instanceof RecognitionException) {
		        reportRecognitionException((RecognitionException) e1.getCause());
		    } else {
		        throw e1;
		    }		    		    
		}else{
		    services.getExceptionHandler().clear();
		}
	    } catch (RecognitionException e) {
	        reportRecognitionException(e);
	    } catch (antlr.ANTLRException e) {
		throw new ProofInputException(e);
	    }	  
	    parseFieldDecl(s.substring(end+1), otherSpecs, cs);
	}else{
	    otherSpecs.add(s);
	}
    }

    /**
     * parses the specifications attached as comments to <code>m</code>.
     */
    protected SetOfJMLMethodSpec parseJMLMethodSpec(ProgramMethod m) 
	throws ProofInputException {
	SetOfJMLMethodSpec result = SetAsListOfJMLMethodSpec.EMPTY_SET;
	if (m.getMethodDeclaration()==null){
	    return result;
	}
	MethodDeclaration md = m.getMethodDeclaration();
	Comment[] comments = md.getComments();
	if(comments != null){
	    for(int i=0; i<comments.length; i++){
		if(comments[i].containsJMLSpec() && 
		   !UsefulTools.isClassSpec(comments[i])){
		    String s = comments[i].getJMLSpec();
		    StringReader stream = new StringReader(s);
		    KeYJMLParser parser = 
			new KeYJMLParser(new KeYJMLLexer(stream),
					 "no file, parsing comment from "+
					 md.getName()+" in class "+
					 cd.getName(),
					 services, nss,
					 TermFactory.DEFAULT, cd, 
					 m, classSpec, aOP, javaPath);
		    try{
			parser.methodspecification();
		    }catch(ExceptionHandlerException e1){
			if(!(e1.getCause() instanceof 
			     NotSupportedExpressionException)){
			    throw e1;
			}else{
			    services.getExceptionHandler().clear();
			}
		    } catch (antlr.ANTLRException e) {
			throw new ProofInputException(e);
		    }
		    result = result.union(parser.getSpecs());
		}
	    }
	}
	parseLoopInvariants(m);
	return result;
    }

    private void parseLoopInvariants(ProgramMethod md)
	throws ProofInputException {
	JavaASTCollector coll = 
	    new JavaASTCollector(md, de.uka.ilkd.key.java.statement.
				 LoopStatement.class);
	coll.start();
	ListOfProgramElement l = coll.getNodes();
	IteratorOfProgramElement it = l.iterator();
	LoopStatement loop;
	while(it.hasNext()){
	    loop = (LoopStatement) it.next();
	    Comment[] comments = loop.getComments();
	    if(comments != null){
		for(int i=0; i<comments.length; i++){
		    if(comments[i].containsJMLSpec()){
			String s = comments[i].getJMLSpec();
			StringReader stream = new StringReader(s);
			KeYJMLParser parser = 
			    new KeYJMLParser(new KeYJMLLexer(stream),
					     "no file, parsing comment from loop"+
					     " in method "+md.getName()+" in class "+
					     cd.getName(),
					     services, nss,
					     TermFactory.DEFAULT, cd, 
					     md, classSpec, aOP, javaPath);
			try{
			    parser.parseLoopInvariant(loop);
			}catch(ExceptionHandlerException e1){
			    if(!(e1.getCause() instanceof 
				 NotSupportedExpressionException)){
				throw e1;
			    }else{
				services.getExceptionHandler().clear();
			    }
			} catch (antlr.ANTLRException e) {
			    throw new ProofInputException(e);
			}
		    }
		}
	    }
	}
    }

    /**
     * returns a mapping from methods to terms that are conjunctions
     * of the proofobligations generated from the methodspecs of these methods
     * obsolete (but for testing reasons still there).
     */
    public HashMap buildProofObligations() throws ProofInputException{
	if(!parsedMethods || !parsedClass){
	    parseSpecs();
	}
	if(method2term != null){
	    return method2term;
	}else{
	    method2term = new LinkedHashMap();
	    Iterator it = method2specs.keySet().iterator();
	    while(it.hasNext()){
		Object m = it.next();
		Term t = makeConjunction((SetOfJMLMethodSpec) 
					 method2specs.get(m), 
					 (ProgramMethod) m);
		if(t!=null){
		    method2term.put(m, t);
		}
	    }
	}
	return method2term;
    }

    /**
     * returns a conjunction of the proofobligations for <code>md</code>
     * generated from <code>specs</code>.
     * obsolete (but for testing reasons still there).
     */
    private Term makeConjunction(SetOfJMLMethodSpec specs, 
				 ProgramMethod md){
	Term result = null;
	Term a, inv, invPre;
	JMLMethodSpec spec;
	if(specs != SetAsListOfJMLMethodSpec.EMPTY_SET){
	    IteratorOfJMLMethodSpec it = specs.iterator();
	    spec = it.next();
	    result = spec.createDLFormula(false, false);
	    inv = classSpec.getPreservesInvariantBehavior(md, false);
	    invPre = spec.getCompletePre(false, false, false);
	    while(it.hasNext()){
		spec = it.next();
		a = spec.createDLFormula(false, false);
		invPre = tb.or(spec.getCompletePre(false, false, false), invPre);
		if(a != null){
		    if(result.op() != Op.TRUE){
			result = tb.and(result, a);
		    }else{
			result = a;
		    }
		}
	    }
	    if(inv != null){
		inv = tb.imp(invPre, inv);
	    }
	    if(result != null && result.op() != Op.TRUE){
		if(inv != null){
		    result = tb.and(result, inv);
		}
	    }else{
		result = inv;
	    }
	// the method has no specification, but maybe it has to preserve
	// invariants, etc.
	// implicit methods need a special treatment.
	}else if(!md.getName().startsWith("<") && (
	       !md.isStatic() &&
	       (classSpec.getInstanceInvariants()!=null ||
		classSpec.getInstanceConstraints()!=null)
	       || classSpec.getStaticConstraints()!=null)
		 || classSpec.getStaticInvariants()!=null
		 && (!md.getName().startsWith("<") || 
		     md.getName().equals(ClassInitializeMethodBuilder.CLASS_INITIALIZE_IDENTIFIER))){
	    result = classSpec.getPreservesInvariantBehavior(md, false);
	}
	return result;
    }

    /**
     * returns a map from methods to the specs which have been parsed by this
     * JMLSpecBuilder.
     */
    public HashMap getMethod2Specs(){
	try{
	    parseSpecs();
	}catch(ProofInputException e){
	    e.printStackTrace();
	}
	return method2specs;
    }

    /**
     * returns a map with the model methods and their specs
     * parsed by this JMLSpecBuilder.
     */
    public HashMap getModelMethod2Specs(){
	try{
	    parseSpecs();
	}catch(ProofInputException e){
	    e.printStackTrace();
	}
	return classSpec.buildModelMethod2Specs();
    }

    /** 
     * Parses the specs of the methods declared in <code>cd</code>
     */
    public void parseJMLMethodSpecs() throws ProofInputException {
    	if(parsedMethods){
    		return;
    	}
    	if(cd.getFullName().indexOf("jmlspecs.models") == -1){
    		KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(cd);
    		ListOfProgramMethod ms = 
		    services.getJavaInfo().getKeYProgModelInfo().
		    getAllProgramMethodsLocallyDeclared(kjt).append(
			services.getJavaInfo().getKeYProgModelInfo().
			getConstructors(kjt)); 
    		IteratorOfProgramMethod it = ms.iterator();
    		while(it.hasNext()){
    			ProgramMethod m = it.next();
    			if(m != null){
    				method2specs.put(m, parseJMLMethodSpec(m));
    			}
    		}	    
    		
    	}
    	IteratorOfNamed mmit = 
    		classSpec.getModelMethods().allElements().iterator();
    	while(mmit.hasNext()){
    		ProgramMethod m = (ProgramMethod) mmit.next();
    		parseJMLMethodSpec(m);
    	}
    	parsedMethods = true;
    }

    private void parseSpecs() throws ProofInputException{
	parseJMLClassSpec();
	parseJMLMethodSpecs();
    }
}	

