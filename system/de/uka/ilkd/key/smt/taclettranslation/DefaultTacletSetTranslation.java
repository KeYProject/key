package de.uka.ilkd.key.smt.taclettranslation;

import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet.VariableSV;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;

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
    private ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();

    /**
     * List of taclet translators. If you want to add translators use
     * <code>add</code>. When a taclet is translated the first translator in the
     * list is chosen which fits the taclet.
     */
    private ImmutableList<TacletTranslator> translators = ImmutableSLList.nil();

    /**
     * List of used heuristics. Use <code>add</code> and <code>remove</code> to
     * change the list.
     */
    private ImmutableList<String> heuristics = ImmutableSLList.nil();
    
    private ImmutableSet<Sort> usedFormulaSorts = DefaultImmutableSet.nil();
    
    private ImmutableSet<Term> usedAttributeTerms = DefaultImmutableSet.nil();
    
    /**
     * Sorts that have been used while translating the set of taclets.
     */
    private HashSet<Sort> usedSorts = new HashSet<Sort>();

    /**
     * Shema variables of the type Variable that have been used while translating the set of taclets.
     */
    private HashSet<QuantifiableVariable> usedQuantifiedVariable = new HashSet<QuantifiableVariable>();
    
    private HashSet<SchemaVariable> usedFormulaSV = new HashSet<SchemaVariable>();

    private boolean quitInstantiationFailuresWithException=false;

    public DefaultTacletSetTranslation(Services services) {
	TacletTranslator tt = new FindTacletTranslator(services);
	tt.addListener(this);
	translators = translators.append(tt);
	
    }

    /**
     * Checks whether the given taclet contains at least one heuristic of the
     * list <code>heuristics</code>.
     * 
     * @param t
     *            taclet to be checked.
     * @return <code>true</code> if the taclet contains one of the given
     *         heuristic otherwise <code>false</code>.
     */
    public boolean checkHeuristic(Taclet t) {
	for (String h : heuristics) {
	    for (RuleSet rs : t.getRuleSets()) {
		if (rs.name().toString().equals(h))
		    return true;
	    }

	}
	return false;
    }

    public ImmutableList<TacletFormula> getTranslation(ImmutableSet<Sort> sorts, 
	    ImmutableSet<Term> attributeTerms) {

	// only translate once a time.
	if (!translate)
	    return translation;
	translate = false;
	usedSorts.clear();
	notTranslated = ImmutableSLList.nil();
	translation = ImmutableSLList.nil();
       
	ImmutableSet<Sort> emptySetSort = DefaultImmutableSet.nil();
	ImmutableSet<Term> emptySetTerm = DefaultImmutableSet.nil();
	usedFormulaSorts = (sorts == null ?emptySetSort :sorts);
	usedAttributeTerms = (attributeTerms == null ? emptySetTerm :attributeTerms);
	
	
	for (Taclet t : taclets) {
	    if (!UsedTaclets.contains(t.name().toString())) {
		// notTranslated = notTranslated.append(new
		// DefaultTacletFormula(t,null,"The taclet is not used for external provers."));
		continue;
	    }
	
	    if (!heuristics.isEmpty() && !checkHeuristic(t)) {

		notTranslated = notTranslated.append(new DefaultTacletFormula(
		        t, null,
		        "The taclet does not have the right heuristic."));
		continue;
	    }
	    int i=0;
	    for (TacletTranslator translator : translators) {
		try { // check for the right translator 
		    translation = translation.append(translator.translate(t,sorts,attributeTerms));
		    break; // translate only once a time.
		} catch (IllegalTacletException e) {
		    if(i == translators.size()-1){
			   notTranslated = notTranslated
			    .append(new DefaultTacletFormula(t, null, e
			            .getMessage()));
		    }
		}
		i++;
	    }
	}

	return translation;
    }

    public void setTacletSet(ImmutableSet<Taclet> set) {
	translate = true;
	translation = ImmutableSLList.nil();
	taclets = set;

    }

    public ImmutableList<TacletFormula> getNotTranslated() {

	return notTranslated;
    }

    public void addHeuristic(String h) {
	heuristics = heuristics.append(h);

    }

    public boolean removeHeursitic(String h) {
	int size = heuristics.size();
	heuristics = heuristics.removeFirst(h);
	return size == heuristics.size() + 1;
    }

    
    public void update() {
	translate = true;
	getTranslation(usedFormulaSorts,usedAttributeTerms);

    }

    /**
     * Stores the translation to a file by using the key-format for problem files.  
     * @param dest the path of the file.
     */
    public void storeToFile(String dest) {
	storeToFile(getTranslation(usedFormulaSorts, usedAttributeTerms), dest);
    }

    private void storeToFile(ImmutableList<TacletFormula> list, String dest) {
        String toStore = "";
        
        if(usedSorts.size() > 0){
            toStore += "\\sorts{\n\n";
            for(Sort sort : usedSorts){
                toStore += sort.name().toString()+";\n";  
            }
            toStore += "}\n\n\n";
    	
        }

        
    /*    if(!usedQuantifiedVariable.isEmpty()){
            toStore += "\\functions{\n\n";
            for(QuantifiableVariable var : usedQuantifiedVariable){
        	toStore += var.sort() + " "+ var.name().toString()+";\n";  
            }
            toStore += "}\n\n\n";
        }*/
        
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
	

	FileWriter fw;
	try {
	    fw = new FileWriter(dest);
	    fw.write(toStore);
	    fw.close();
	} catch (IOException e) {
	    // TODO: handling the exception
	}

    }

    private String convertTerm(Term term) {
	return LogicPrinter.quickPrintTerm(term, null);
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
	String s = "";
	s += "taclet: " + t.name()+"\n";
	s += "term: " + term +"\n"; 
	s += "generic sort: " + dest + "\n";
	s += "sort: "+ sort +"\n";
	instantiationFailures = instantiationFailures.append(s);
	return quitInstantiationFailuresWithException ;
    }







}
