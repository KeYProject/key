// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.taclettranslation.assumptions;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Calendar;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.IllegalTacletException;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

public final class DefaultTacletSetTranslation 
			implements TacletSetTranslation,TranslationListener {

    /**
     * if <code>translate</code> is <code>true</code> the method
     * <code>getTranslation()</code> will first translate the given taclets
     * before it returns <code>translation</code>.
     */
    private boolean translate = false;

    /**
     * Translation of the taclets stored in <code>taclets</code>.
     * 
     * */
    private ImmutableList<TacletFormula> translation = ImmutableSLList.nil();

    /**
     * Taclets can not be translated because checking the taclet failed.
     */
    private ImmutableList<TacletFormula> notTranslated = ImmutableSLList.nil();
    
    /**
     * If a instantiation failure occurs the returned information is stored
     * in a String.
     */
    private ImmutableList<String> instantiationFailures = ImmutableSLList.nil();

    /**
     * List of taclets that should be translated. The translation will be done
     * by calling <code>getTtranslation()</code>.
     */
    private Collection<Taclet> taclets = new LinkedList<Taclet>();


    private final AssumptionGenerator assumptionGenerator;
    

    
    private ImmutableSet<Sort> usedFormulaSorts = DefaultImmutableSet.nil();
    

    /**
     * Sorts that have been used while translating the set of taclets.
     */
    private HashSet<Sort> usedSorts = new HashSet<Sort>();

    /**
     * Shema variables of the type Variable that have been used while translating the set of taclets.
     */
    private HashSet<QuantifiableVariable> usedQuantifiedVariable = new HashSet<QuantifiableVariable>();
    
    private Services services;
    
    private HashSet<SchemaVariable> usedFormulaSV = new HashSet<SchemaVariable>();

    private boolean quitInstantiationFailuresWithException=false;
    
    private int maxGeneric =2;

    public DefaultTacletSetTranslation(Services services) {
	assumptionGenerator = new AssumptionGenerator(services);
	assumptionGenerator.addListener(this);
	
	//translators = translators.append(tt);
	this.services = services;
	
    }


    


    public ImmutableList<TacletFormula> getTranslation(ImmutableSet<Sort> sorts, int max) {
	this.maxGeneric = max;
	// only translate once.
	if (!translate)
	    return translation;
	translate = false;
	usedSorts.clear();
	notTranslated = ImmutableSLList.nil();
	translation = ImmutableSLList.nil();
       
	ImmutableSet<Sort> emptySetSort = DefaultImmutableSet.nil();

	usedFormulaSorts = (sorts == null ?emptySetSort :sorts);
	

	for (Taclet t : taclets) {
	    
	    if (SupportedTaclets.INSTANCE.contains(t.name().toString())) {
	
	     try{
		 TacletFormula result = 
        	assumptionGenerator.translate(t, sorts, max);
		 translation = translation.append(result);
            
	     } catch(IllegalTacletException e){
		 notTranslated = notTranslated
		    .append(new AssumptionFormula(t, null, e
		            .getMessage())); 
	     }
	    }
	}

	return translation;
    }

    public void setTacletSet(Collection<Taclet> set) {
	translate = true;
	translation = ImmutableSLList.nil();
	taclets = set;

    }

    public ImmutableList<TacletFormula> getNotTranslated() {

	return notTranslated;
    }


    
    public void update() {
	translate = true;
	getTranslation(usedFormulaSorts,maxGeneric);

    }

    /**
     * Stores the translation to a file by using the key-format for problem files.  
     * @param dest the path of the file.
     */
    public void storeToFile(String dest) {

	FileWriter fw;
	try {
	    fw = new FileWriter(dest);
	    fw.write(toString());
	    fw.close();
	} catch (IOException e) {
	    throw new RuntimeException(e);
	}

    }
    
    public String toString(){
	ImmutableList<TacletFormula> list = getTranslation(usedFormulaSorts, maxGeneric);
        String toStore = "";
        toStore = "//"+Calendar.getInstance().getTime().toString()+"\n";
        
        String modelDir = services.getProof().env().getJavaModel().getModelDir();
        
        if(modelDir != "" && modelDir != null){
            toStore += "\\javaSource \""+modelDir+"\";\n\n";
        }
        
        if(usedSorts.size() > 0){
            toStore += "\\sorts{\n\n";
            for(Sort sort : usedFormulaSorts){
        	    String name="";
        	 //TODO: uncomment
//        	    if(sort instanceof ArraySortImpl){
//        		name = ((ArraySortImpl)sort).elementSort().toString();
//        	    }else{
        		name = sort.name().toString();
//        	    }
        		 
        	
              	    toStore += name+";\n";  
        	
               
            }
            toStore += "}\n\n\n";
    	
        }

        

        

        
        
        if(!usedFormulaSV.isEmpty()){
            toStore += "\\predicates{\n\n";
            for(SchemaVariable var : usedFormulaSV){
        	toStore +=  var.name().toString()+";\n";  
            }
            toStore += "}\n\n\n";
        }
        
      
     

      
	toStore += "\\problem{\n\n";
	int i = 0;
	for (TacletFormula tf : list) {
	    toStore += "//" + tf.getTaclet().name().toString() + "\n";
	    toStore += convertTerm(tf.getFormula());
	    if (i != list.size() - 1)
		toStore += "\n\n& //and\n\n";
	    i++;

	}

	toStore += "}";
	
	
	if(notTranslated.size() > 0){
	    toStore += "\n\n// not translated:\n";
	    for(TacletFormula tf : notTranslated){
		toStore += "\n//"+tf.getTaclet().name()+": "+tf.getStatus();
	    }
	}
	
	if(instantiationFailures.size() > 0){
	    toStore += "\n\n/* instantiation failures:\n";
	    for(String s : instantiationFailures){
		toStore += "\n\n"+s;
	    }
	    toStore +="\n\n*/";
	}
	return toStore;
    }

    private String convertTerm(Term term) {
	String ret = LogicPrinter.quickPrintTerm(term, null);
	ret = "("+ret+")";
	return ret;
    }


    public void eventSort(Sort sort) {
	usedSorts.add(sort);
	
    }

  
    public void eventQuantifiedVariable(QuantifiableVariable var) {
	usedQuantifiedVariable.add(var);
	
    }


    public void eventFormulaSV(SchemaVariable formula) {
	usedFormulaSV.add(formula);
	
    }


    public boolean eventInstantiationFailure(GenericSort dest, Sort sort,
            Taclet t, Term term) {
	/*String s = "";
	s += "taclet: " + t.name()+"\n";
	s += "term: " + term +"\n"; 
	s += "generic sort: " + dest + "\n";
	s += "sort: "+ sort +"\n";
	instantiationFailures = instantiationFailures.append(s);*/
	return quitInstantiationFailuresWithException ;
    }







}
