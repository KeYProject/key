// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// 
package de.uka.ilkd.key.smt.taclettranslation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.BoundedNumericalQuantifier;
import de.uka.ilkd.key.logic.op.CastFunctionSymbol;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableAdapter;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.op.WarySubstOp;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.ClassInstanceSort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;

import de.uka.ilkd.key.parser.SchemaVariableModifierSet.TermSV;
import de.uka.ilkd.key.parser.SchemaVariableModifierSet.VariableSV;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.AbstractOrInterfaceType;
import de.uka.ilkd.key.rule.conditions.TypeComparisionCondition;
import de.uka.ilkd.key.rule.conditions.TypeCondition;

abstract class AbstractTacletTranslator implements TacletTranslator {

    protected final static TermFactory tf = TermFactory.DEFAULT;
    
    

    protected HashMap<String, LogicVariable> usedVariables = 
	new HashMap<String, LogicVariable>();
    protected HashMap<String, VariableSV> usedSchemaVariables = new HashMap<String, VariableSV>();
    
    private HashSet<GenericSort> usedGenericSorts = new HashSet<GenericSort>();

    protected Collection<TranslationListener> listener= new LinkedList<TranslationListener>();
    
    protected TacletConditions conditions; 
        
    
    public TacletFormula translate(Taclet t, ImmutableSet<Sort> sorts)
    throws IllegalTacletException{
	
	// first step: check the taclet. If this translator is not able 
	// to translate the taclet throw IllegalTacletException.
	check(t);
	
	
	// second step: determine the variable conditions.
	this.conditions = new TacletConditions(t);
	
	
	//  third step: translate the taclet, but do not translate generic variables 
	// and do not quantify the variables.
	Term term = translateTaclet(t,sorts);
	
	
	
	
	// fourth step: rebuild the term to exchange schema variables with logic varibales.
	usedGenericSorts = new HashSet<GenericSort>();
	term = rebuildTerm(term);
	
	
	// fifth step: quantify all free variables.
	term = quantifyTerm(term);
	

	// sixth step: translate the generics sorts.
	term = translateGeneric(term,usedGenericSorts,sorts);
	
	
	

	
	
	
	
	TacletFormula tf = new DefaultTacletFormula(t, term, "",conditions);
	return tf;
    }
    
    /**
     * Override this method to introduce a translating mechanism for taclets.
     * This mechanism should not translate generic types. This will be done 
     * by <code>translateGeneric</code>.  
     * @param t taclet to be translated.
     * @param sorts the sorts that are used in the current proof.
     * @return returns the translation of the taclet.
     */
    protected abstract Term translateTaclet(Taclet t,ImmutableSet<Sort> sorts)
    throws IllegalTacletException;

    /**
     * Translates a sequent to a term by using the following translations rules:
     * T ==> D is translated to: And(T)->Or(D).<br>
     * And(s): conjunction between all formulae in set s. Or(s): disjunction
     * between all formulae in set s.
     * 
     * @param s
     *            The sequent to be translated.
     * @return the resulting term of the translation or <code>null</code> if
     *         both antecedent and succendent are empty.
     */
    protected Term translate(Sequent s) {
	TermBuilder builder = TermBuilder.DF;

	ImmutableList<Term> ante = getFormulaeOfSemisequent(s.antecedent());
	ImmutableList<Term> succ = getFormulaeOfSemisequent(s.succedent());

	if (ante.size() == 0 && succ.size() == 0)
	    return null;
	if (succ.size() == 0)
	    return builder.not(builder.and(ante));
	if (ante.size() == 0)
	    return builder.or(succ);
	
	return builder.imp(builder.and(ante), builder.or(succ));
    }
    
    
    /**
     * Translates generic variables. 
     * @param currentTerm 
     * @param genericSorts
     * @param sorts
     * @return
     * @throws IllegalTacletException
     */
    protected Term translateGeneric(Term currentTerm,HashSet<GenericSort> genericSorts, ImmutableSet<Sort> sorts)
    throws IllegalTacletException{
	return instantiateGeneric(currentTerm, genericSorts, sorts);
    }

    /**
     * Because the taclet translation follows a bottom up approach, there are
     * taclets that can not be translated yet. This method check whether there
     * are general conditions that make a translation impossible.
     * 
     * @param t
     *            Taclet to be checked
     * @throws IllegalTacletException
     *             if the taclet can not be translated because of general
     *             reasons.
     */
    protected void checkGeneralConditions(Taclet t)
	    throws IllegalTacletException {

	Iterator<VariableCondition> it = t.getVariableConditions();
	while(it.hasNext()){
	    VariableCondition vc = it.next();
	    //TODO: uncomment this field - only for testing
	    if(!(vc instanceof TypeComparisionCondition)&&
	       !(vc instanceof TypeCondition) &&
	       !(vc instanceof AbstractOrInterfaceType) )
	       {
		throw new IllegalTacletException(
			"The taclet has at least one variable condition" +
			" that is not supported: " + vc.toString() );
	    }
	}
	

	if (t.varsNotFreeIn().hasNext()) {
	    throw new IllegalTacletException(
		    "The taclet has \\notFreeIn conditions.");
	}
	

	// Check for addrules, they are in general not allowed.
	checkGoalTemplates(t);

	// Check the assume-sequent.
	checkSequent(t.ifSequent());
    }

    /**
     * Checks whether the taclet has addrules.<br>
     * 
     * @param t
     *            taclet to be checked.
     * @throws IllegalTacletException
     *             if the taclet is not translatable.
     */
    private void checkGoalTemplates(Taclet t) throws IllegalTacletException {
	for (TacletGoalTemplate template : t.goalTemplates()) {
	    if (template.rules().size() > 0) {
		throw new IllegalTacletException("The taclet has addrules.");
	    }
	    // Check the add-sequent of the goal template
	    checkSequent(template.sequent());
	    // If the subclass must check the template, too:
	    // delegate the check to the subclass.
	    checkGoalTemplate(template);
	}

    }

    /**
     * Override this method if you want to check a goal template in a sub class.
     * 
     * @param template
     * @throws IllegalTacletException
     *             if the template is not translatable.
     */
    protected void checkGoalTemplate(TacletGoalTemplate template)
	    throws IllegalTacletException {
    }

    /**
     * Checks the sequent by checking every term within in this sequent.
     * 
     * @param s
     * @throws IllegalTacletException
     *             if the sequent is not supported.
     */
    protected void checkSequent(Sequent s) throws IllegalTacletException {
	for (ConstrainedFormula cf : s) {
	    checkTerm(cf.formula());
	}

    }

    /**
     * Checks whether a operator is supported. This method contains operators
     * every taclet should support. Override this method if a special taclet
     * should support more operators.
     * 
     * @param op
     *            the operator to be checked.
     * @throws IllegalTacletException
     *             if the operator is not supported.
     */

    protected void checkOperator(Operator op) throws IllegalTacletException {
	
	if ((op instanceof Junctor)
	        || (op instanceof Equality)
	        || (op instanceof Quantifier)
	        || (op instanceof RigidFunction)
	        || (op instanceof IfThenElse)
	        || ((op instanceof SchemaVariableAdapter) &&
	        	((SchemaVariableAdapter) op).isTermSV())
	        || ((op instanceof SchemaVariableAdapter) && 
	        	((SchemaVariableAdapter) op).isFormulaSV())
	        || ((op instanceof WarySubstOp))

	        
	

	) {
	    return;
	}
	throw new IllegalTacletException("The operator " + op.toString()
	        + " is not supported. Class: " + op.getClass().getName());

    }

    /**
     * Checks the given term by checking the operator of the term and by
     * checking the subterms.
     * 
     * @param term
     *            the operator to be checked.
     * @throws IllegalTacletException
     *             if the term is not supported.
     */
    protected void checkTerm(Term term) throws IllegalTacletException {
	checkOperator(term.op());
	for(TranslationListener l : listener){
	    if(term.sort() != null && !(term.sort() instanceof GenericSort)){
		if(term.sort().equals(Sort.FORMULA)){
		    if(((term.op() instanceof SchemaVariableAdapter) &&
			    ((SchemaVariableAdapter) term.op())
		                .isFormulaSV())){
			 l.eventFormulaSV((SchemaVariable) term.op());
		    }

		}else{
		    l.eventSort(term.sort());
		}
		
	    }
	}
	for (int i = 0; i < term.arity(); i++) {
	    checkTerm(term.sub(i));
	}
    }

    /**
     * Collects all formulae of a semisequent in a set.
     * 
     * @param s
     *            Semisequent.
     * @return A list of all formulae of the semisequent <code>s </code>.
     */
    private ImmutableList<Term> getFormulaeOfSemisequent(Semisequent s) {
	ImmutableList<Term> terms = ImmutableSLList.nil();
	for (ConstrainedFormula cf : s) {
	    terms = terms.append(cf.formula());
	}
	return terms;

    }

    /**
     * Use this method to rebuild the given term. The method splits the term in
     * its single components and assemblies them. After every splitting step the
     * method calls <code>changeTerm</code>. This mechanism can be used to
     * exchange subterms.
     * 
     * @param term the term to rebuild.
     * @param genericSorts for the translation of generic variables. 
     * @return returns the new term.
     */
   
    protected Term rebuildTerm(Term term){
	
	ImmutableArray<QuantifiableVariable> variables[] = new ImmutableArray[term
	                                                                      .arity()];
	Term[] subTerms = new Term[term.arity()];

	

	for (int i = 0; i < term.arity(); i++) {
	    variables[i] = term.varsBoundHere(i);//subTerms[i].varsBoundHere(i);
	    subTerms[i] = rebuildTerm(term.sub(i));
	    
	}

	term = changeTerm(term);
	
	
	if(term.op() instanceof Quantifier){
	       
	  
	   // ImmutableArray<QuantifiableVariable> temp = new ImmutableArray<QuantifiableVariable>(); 
	    QuantifiableVariable [] temp = new QuantifiableVariable[variables[0].size()];
	    int i=0;
	    for(QuantifiableVariable qv : variables[0]){
		    for(TranslationListener l : listener){
			    l.eventQuantifiedVariable(qv);
			}
	    }	    
	}


	term = tf.createTerm(term.op(), subTerms, variables,
		JavaBlock.EMPTY_JAVABLOCK);
	return term;
    }
    

    
    /**
     * Instantiates all variables of a generic sort with 
     * logical variables in the given term.
     * @param term the term to instantiate.
     * @param genericSort generic sort to instantiate.
     * @param sorts sorts used for instantiation.
     * @return returns list of terms that are instantiated with 
     * the given generic sort.
     */
    protected ImmutableList<Term> instantiateGeneric(Term term, 
	    GenericSort genericSort, ImmutableSet<Sort> sorts){
	ImmutableList<Term> genericTerms = ImmutableSLList.nil();
	
	for(Sort sort : sorts){
	    if(sort instanceof GenericSort){continue;}
	      Term temp = instantiateGeneric(term, genericSort, sort);
	    if(temp != null){
		    genericTerms = genericTerms.append(temp);
	    }
	
	    
	}
	
	return genericTerms;
    }
   
    
    private LogicVariable getInstantiationOfLogicVar(Sort instantiation, LogicVariable lv){
	

	LogicVariable res = getLogicVariable(new Name(instantiation.name()
	        .toString()
	        + "__" + lv.name().toString()), instantiation);
	for (TranslationListener l : listener) {
	    l.eventSort(instantiation);
	}
	return res;
    }
    
    /**
     * Instantiates all variables of a generic sort with logic variables. 
     * The logic variable has the same name with the prefix [sort]__
     * @param term 
     * @param generic the generic sort that should be instantiated. 
     * @param instantiation the instantiation sort.
     * @return returns the new term with instantiated variables. If <code>term</code>
     * can not be instantiated the method returns <code>null</code>, e.g. this can occur,
     * when <code>term</code> is of type {@link SortDependingFunction} and 
     * <code>instantiation</code> is of type {@link PrimitiveSort}.
     */
    
    protected Term instantiateGeneric(Term term, GenericSort generic,
	    Sort instantiation) throws IllegalArgumentException {
	ImmutableArray<QuantifiableVariable> variables[] = new ImmutableArray[term
	        .arity()];
	Term[] subTerms = new Term[term.arity()];
	for (int i = 0; i < term.arity(); i++) {
	    subTerms[i] = instantiateGeneric(term.sub(i), generic,
		    instantiation);
	    if (subTerms[i] == null) {
		return null;
	    }
	    variables[i] = subTerms[i].varsBoundHere(i);
	}

	if (term.sort().equals(generic)) {

	    if (term.op() instanceof LogicVariable) {
		TermBuilder tb = TermBuilder.DF;
		term = tb.var(getInstantiationOfLogicVar(instantiation,(LogicVariable)term.op()));
	    }  else if (term.op() instanceof SchemaVariable){
		if(((SchemaVariable)term.op()).isTermSV()){
			term = TermBuilder.DF.var(getInstantiationOfLogicVar(instantiation,getLogicVariable(term.op().name(),term.sort())));   
		}
	
		//term = TermFactory.DEFAULT.createTerm(new TermSV(), subTerms, variables, JavaBlock.EMPTY_JAVABLOCK);
	    }
	    else if (term.op() instanceof CastFunctionSymbol) {
		term = TermFactory.DEFAULT.createCastTerm(
		        (AbstractSort) instantiation, subTerms[0]);
	    }   
	    
	    else if (term.op() instanceof SortDependingFunction) {
		SortDependingFunction func = (SortDependingFunction) term.op();

		// SortDependingFunctions can not be instantiated with primitive
		// sorts.
		if ((instantiation instanceof PrimitiveSort)) {
		    return null;
		} else {
		    term = tf
			    .createFunctionTerm(
			            (SortDependingFunction) func
			                    .getInstanceFor((SortDefiningSymbols) instantiation),
			            subTerms);
		}

	    }

	}
	
	
	if(term.op() instanceof Quantifier){
	    QuantifiableVariable [] copy = new QuantifiableVariable[term.varsBoundHere(0).size()]; 
	    int i=0; 
	    
	    for(QuantifiableVariable var : term.varsBoundHere(0)){
		copy[i] = var;
		if(copy[i].sort() instanceof GenericSort){
		    copy[i] = getLogicVariable(copy[i].name(),instantiation);
		}
	
		i++;
	    }
	    term = TermBuilder.DF.all(copy,subTerms[0]);

	}else{
	    term = tf.createTerm(term.op(), subTerms, variables,
		        JavaBlock.EMPTY_JAVABLOCK);
	}	
	return term;

    }
    
    
    private boolean isReferenceSort(Sort sort){
	return  ( sort instanceof ClassInstanceSort );
    }
    
    /**
     * Tests sort of its instantiation ability.
     * @param sort sort to be tested.
     * @return <code>true</code> if can be instantiated,
     *  otherwise <code>false</code>
     */
    private boolean doInstantiation(GenericSort generic, Sort inst){
	
	return !( (inst instanceof GenericSort)
		|| (inst.equals(Sort.ANY)) 
		|| (conditions.containsIsReferenceCondition(generic)
			>0
			&& !isReferenceSort(inst)));
    }
    

    /**
     * Instantiates generic variables of the term. 
     * It instantiates the variables using
     * all possibilities. This method supports two different 
     * generic variables and the following variable conditions:
     * - \not\same(G,H)
     * @param term the term to be instantiated.
     * @param genericSorts the generic sorts that should be replaced.
     * @param instSorts the instantiations
     * @return returns a new term, where all generic variables
     * are instantiated. If there is no generic variable the original term
     * is returned.
     * @throws IllegalTacletException
     */
    protected Term instantiateGeneric(Term term, 
	    HashSet<GenericSort> genericSorts, ImmutableSet<Sort> instSorts) 
	    throws IllegalTacletException{
	if(genericSorts.size() == 0){return term;}
	  if(genericSorts.size() > 2){
	    throw new 
	    IllegalTacletException("Can not translate taclets with " +
	    		"more than two generic sorts.");}
	
	ImmutableList<Term> genericTerms = ImmutableSLList.nil();
	
	GenericSort gs [] = new GenericSort[2];
	int i=0;
	for(GenericSort sort : genericSorts){
	    gs[i]= sort;
	    i++;
	}

	// instantiate the first generic variable
	for(Sort sort1 : instSorts){
	   
	    if(!doInstantiation(gs[0],sort1)){continue;}
		  
	    Term temp = instantiateGeneric(term, gs[0], sort1);

	    if(temp == null){continue;}
	    
	    //instantiate the second generic variable
	    if(genericSorts.size() == 2){
		int instCount =0;
		
		for(Sort sort2 : instSorts){

		   if(!(conditions.containsNotSameCondition(gs[0], gs[1]) && 
			   sort1.equals(sort2)) && 
			   doInstantiation(gs[1],sort2)){
	
		            Term temp2 = instantiateGeneric(temp,gs[1],sort2);
		       	    if(temp2 !=null){
		       		instCount++;
		       		genericTerms = genericTerms.append(temp2);
		       	    }
		       	 
			} 
		    
		}
		if(instCount == 0){
		    throw new 
		    IllegalTacletException("Can not instantiate generic variables" +
			" because there are not enough different sorts.");
		}
	
	    }else{
		genericTerms = genericTerms.append(temp);
	    }
	    
	 
	}
	
	if(genericTerms.size() == 0){
		throw new 
		IllegalTacletException("Can not instantiate generic variables" +
		" because there are not enough different sorts.");
	} 
	

	// quantify the term
	ImmutableList<Term> genericTermsQuantified = ImmutableSLList.nil();
	if(genericTerms.size() > 0){
	     for(Term gt : genericTerms){
		genericTermsQuantified = genericTermsQuantified.append(quantifyTerm(gt)); 
		
	    }
	    term = TermBuilder.DF.and(genericTermsQuantified);
	    
	}
	
	
	
	return  term;
    }
    
    
    /**
     * Quantifies a term, i.d. every free variable is bounded by a allquantor. 
     * @param term the term to be quantify.
     * @return the quantified term.
     */
     protected Term quantifyTerm(Term term){
	TermBuilder tb = TermBuilder.DF;
	// Quantify over all free variables.
	for (QuantifiableVariable qv : term.freeVars()) {
	  // if(!term.sort().equals(Sort.FORMULA)){
	    term = tb.all(qv, term);

	  // }
	}
	return term;
    }
    
    

    
    

    /**
     * Returns a new logic variable with the given name and sort. If already a
     * logic variable exists with the same name and sort this variable is
     * returned instead of a new logic variable.
     * 
     * @param name
     *            name of the logic variable.
     * @param sort
     *            sort of the logic variable.
     * @return logic variable with the given name and sort.
     */
    protected LogicVariable getLogicVariable(Name name, Sort sort) {
	name = new Name(eliminateSpecialChars(name.toString()));
	LogicVariable l = usedVariables.get(name.toString());
	if (l == null) {
	    
	    l = new LogicVariable(name, sort);
	    usedVariables.put(name.toString(), l);
	}
	return l;

    }
    
    protected String eliminateSpecialChars(String name) {
	StringBuffer toReturn = new StringBuffer(name);
	
	//build the replacement pairs
	ArrayList<String> toReplace = new ArrayList<String>();
	ArrayList<String> replacement = new ArrayList<String>();
	
	toReplace.add("[]");
	replacement.add("_Array");
	
	
	toReplace.add(".");
	replacement.add("_dot_");
	
	toReplace.add(":");
	replacement.add("_col_");
	
	
	
	toReturn = this.removeIllegalChars(toReturn, toReplace, replacement);

	return toReturn.toString();
    }
    
    private StringBuffer removeIllegalChars(StringBuffer template, ArrayList<String> toReplace, ArrayList<String> replacement) {
	//replace one String
	for (int i = 0; i < toReplace.size(); i++) {
	    String toRep = toReplace.get(i);
	    String replace = replacement.get(i);
	    int index = template.indexOf(toRep);
	    while (index >= 0) {
		template.replace(index, index + toRep.length(), replace);
		index = template.indexOf(toRep);
	    }
	}
	
	return template;
    }
    

    /**
     * Override this method if you want to change the term, i.e. exchanging
     * schema variables with logic variables. See <code>rebuildTerm</code>.
     * 
     * @param term
     *            the term to be changed.
     * @return the new term.
     */
    protected Term changeTerm(Term term) {
	
	
	TermBuilder tb = TermBuilder.DF;


		
	if(term.op() instanceof SortedSchemaVariable) {
	    if(term.sort().equals(Sort.FORMULA)){

	//	term = tb.var(getLogicVariable(term.op().name(),Sort.FORMULA));
		//term = tb.var(getLogicVariable(term.op().name(),term.sort()));
	    }else if(!(term.sort() instanceof GenericSort)){

		term = tb.var(getLogicVariable(term.op().name(), term.sort()));
	    }
	    
	}
	if(term.sort() instanceof GenericSort){
	    usedGenericSorts.add((GenericSort) term.sort());   
	}
	return term;
    }
    
    public void addListener(TranslationListener listener){
	this.listener.add(listener);
    }
    
    public void removeListener(TranslationListener listener){
	this.listener.remove(listener);
    }

    /**
     * @param t
     * @throws IllegalTacletException
     */
    protected abstract void check(Taclet t) throws IllegalTacletException;

}
