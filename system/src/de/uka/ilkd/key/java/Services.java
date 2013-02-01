// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java;

import java.util.HashMap;

import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.SchemaCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.InnerVariableNamer;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.proof.Counter;
import de.uka.ilkd.key.proof.NameRecorder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

/**
 * this is a collection of common services to the KeY prover. Services
 * include information on the underlying Java model and a converter to
 * transform Java program elements to logic (where possible) and back.
 */
public class Services{
    
    /**
     * the proof
     */
    private Proof proof;

    /**
     * proof specific namespaces (functions, predicates, sorts, variables)
     */
    private NamespaceSet namespaces = new NamespaceSet();

    /** used to determine whether an expression is a compile-time 
     * constant and if so the type and result of the expression
     */
    private ConstantExpressionEvaluator cee;

    /** used to convert types, expressions and so on to logic elements
     * (in special into to terms or formulas)
     */
    private TypeConverter typeconverter;

    /**
     * the information object on the Java model
     */
    private final JavaInfo javainfo;
        
    /**
     * variable namer for inner renaming
     */
    private final VariableNamer innerVarNamer = new InnerVariableNamer(this);

    /**
     * the exception-handler
     */
    private KeYExceptionHandler exceptionHandler;
    

    /**
     * map of names to counters
     */
    private HashMap<String, Counter> counters = new HashMap<String, Counter>();

    /**
     * specification repository
     */
    private SpecificationRepository specRepos 
    	= new SpecificationRepository(this);
    

    private NameRecorder nameRecorder;
    
    
    /**
     * creates a new Services object with a new TypeConverter and a new
     * JavaInfo object with no information stored at none of these.
     */
    public Services(KeYExceptionHandler exceptionHandler){
	cee = new ConstantExpressionEvaluator(this);
        typeconverter = new TypeConverter(this);
	if(exceptionHandler == null){
	    this.exceptionHandler = new KeYRecoderExcHandler();
	}else{
	    this.exceptionHandler = exceptionHandler;
	}
        javainfo = new JavaInfo
        	(new KeYProgModelInfo(this, typeconverter, this.exceptionHandler), this);
        nameRecorder = new NameRecorder();
    }
    
    
    // ONLY for tests
    public Services() { 
	this((KeYExceptionHandler) null);
    }    
    

    private Services(KeYCrossReferenceServiceConfiguration crsc, 
		     KeYRecoderMapping rec2key) {
	cee = new ConstantExpressionEvaluator(this);
	typeconverter = new TypeConverter(this);
	//	exceptionHandler = new KeYRecoderExcHandler();
	javainfo = new JavaInfo
	    (new KeYProgModelInfo(this, crsc, rec2key, typeconverter), this);
	nameRecorder = new NameRecorder();
    }

    
    public KeYExceptionHandler getExceptionHandler(){
	return exceptionHandler;
    }
    

    public void setExceptionHandler(KeYExceptionHandler keh){
	exceptionHandler = keh;
    }

    
    /**
     * Returns the TypeConverter associated with this Services object.
     */
    public TypeConverter getTypeConverter(){
        return typeconverter;
    }

    
    private void setTypeConverter(TypeConverter tc) {
	typeconverter = tc;
    }

    
    /**
     * Returns the ConstantExpressionEvaluator associated with this Services object.
     */
    public ConstantExpressionEvaluator getConstantExpressionEvaluator() {
        return cee;
    }

    
    /**
     * Returns the JavaInfo associated with this Services object.
     */
    public JavaInfo getJavaInfo() {
        return javainfo;
    }
    
    
    public NameRecorder getNameRecorder() {
        return nameRecorder;
    }

    
    public void saveNameRecorder(Node n) {
        n.setNameRecorder(nameRecorder);
        nameRecorder = new NameRecorder();
    }

    
    public void addNameProposal(Name proposal) {
        nameRecorder.addProposal(proposal);
    }
    
    
    public SpecificationRepository getSpecificationRepository() {
	return specRepos;
    }
    
    
    /**
     * Returns the VariableNamer associated with this Services object.
     */
    public VariableNamer getVariableNamer() {
        return innerVarNamer;
    }
    

    /**
     * creates a new services object containing a copy of the java info of
     * this object and a new TypeConverter (shallow copy)
     * @return the copy
     */
    public Services copy() {
	Debug.assertTrue
	    (!(getJavaInfo().getKeYProgModelInfo().getServConf() 
	       instanceof SchemaCrossReferenceServiceConfiguration),
	     "services: tried to copy schema cross reference service config.");
	Services s = new Services
	    (getJavaInfo().getKeYProgModelInfo().getServConf(),
	     getJavaInfo().getKeYProgModelInfo().rec2key().copy());
        s.specRepos = specRepos;
	s.setTypeConverter(getTypeConverter().copy(s));
	s.setExceptionHandler(getExceptionHandler());
	s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
	return s;
    }
    

    /**
     * creates a new service object with the same ldt information 
     * as the actual one
     */
    public Services copyPreservesLDTInformation() {
	Debug.assertTrue
	    (!(javainfo.getKeYProgModelInfo().getServConf() 
	       instanceof SchemaCrossReferenceServiceConfiguration),
	     "services: tried to copy schema cross reference service config.");
	Services s = new Services(getExceptionHandler());
	s.setTypeConverter(getTypeConverter().copy(s));
	s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
	return s;
    }
    
    
    public Services copyProofSpecific(Proof p_proof) {
        final Services s = new Services(getJavaInfo().getKeYProgModelInfo().getServConf(),
                getJavaInfo().getKeYProgModelInfo().rec2key());
        s.proof = p_proof;
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setExceptionHandler(getExceptionHandler());
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        return s;
    }

    
    /*
     * returns an existing named counter, creates a new one otherwise
     */
    public Counter getCounter(String name) {
        Counter c = counters.get(name);
        if (c != null) return c;
        c = new Counter(name);
        counters.put(name, c);
        return c;
    }

    /**
     * returns the namespaces for functions, predicates etc.
     * @return the proof specific namespaces
     */
    public NamespaceSet getNamespaces() {
        return namespaces;
    }
    
    
    /**
     * sets the namespaces of known predicates, functions, variables
     * @param namespaces the NamespaceSet with the proof specific namespaces
     */
    public void setNamespaces(NamespaceSet namespaces) {
        this.namespaces = namespaces;
    }
    
    
    /**
     * Returns the proof to which this object belongs, or null if it does not 
     * belong to any proof.
     */
    public Proof getProof() {
	return proof;
    }

}
