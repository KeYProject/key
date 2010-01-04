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

import java.io.StringWriter;
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

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.ExactInstanceof;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.BoundedNumericalQuantifier;
import de.uka.ilkd.key.logic.op.CastFunctionSymbol;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.ExactInstanceSymbol;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.InstanceofSymbol;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.NonRigidHeapDependentFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableAdapter;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.op.WarySubstOp;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ClassInstanceSort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;



import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletGoalTemplate;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.AbstractOrInterfaceType;
import de.uka.ilkd.key.rule.conditions.ArrayComponentTypeCondition;
import de.uka.ilkd.key.rule.conditions.TypeComparisionCondition;
import de.uka.ilkd.key.rule.conditions.TypeCondition;
import de.uka.ilkd.key.rule.metaconstruct.MetaCreated;
import de.uka.ilkd.key.rule.metaconstruct.MetaNextToCreate;

interface VariablePool{
    LogicVariable getInstantiationOfLogicVar(Sort instantiation, LogicVariable lv);
    LogicVariable getLogicVariable(Name name, Sort sort);
}

abstract class AbstractTacletTranslator implements TacletTranslator,VariablePool {
    
    // only for testing. 
   // private boolean appendGenericTerm = false;

    protected final static TermFactory tf = TermFactory.DEFAULT;
    
    

    protected HashMap<String, LogicVariable> usedVariables = 
	new HashMap<String, LogicVariable>();
  //  protected HashMap<String, VariableSV> usedSchemaVariables = new HashMap<String, VariableSV>();
    
    private HashSet<GenericSort> usedGenericSorts = new HashSet<GenericSort>();

    protected Collection<TranslationListener> listener= new LinkedList<TranslationListener>();
    
    protected TacletConditions conditions; 
    private Services services;
    
    private GenericTranslator genericTranslator = new GenericTranslator(this);
 
    
    AbstractTacletTranslator(Services services){
	this.services = services;

    }
    
    private boolean isCreatedTerm(Term term){
	if(term.op() instanceof MetaCreated){
	    return true;
	}
	if(term.op() instanceof AttributeOp){
	    AttributeOp op = (AttributeOp) term.op();
	    if(op.sort().equals(ProgramSVSort.IMPLICITCREATED)){
		return true;
	    }
	    final KeYJavaType objectKJT = services.getJavaInfo().getJavaLangObject();
	    if(op.attribute().equals(
		    services.getJavaInfo().
		    getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, objectKJT))){
		return true;
	    }
		
	}
	return false;
    }
    
    public TacletFormula translate(Taclet t, ImmutableSet<Sort> sorts,
	    ImmutableSet<Term> attributeTerms)  throws IllegalTacletException{
	
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
	// translate attributes
	
	ImmutableSet<Term>result  = AttributeTranslator.DEFAULT
		.translate(t,term,attributeTerms,services,conditions);
	
	
	
	if(!result.isEmpty()){
	    Term [] array = new Term[result.size()];
	    result.toArray(array);
	    term = TermBuilder.DF.tt();
	    for(Term tmp : result){
		if(checkForNotInstantiatedAttributes(tmp)){
		    term = TermBuilder.DF.and(term,tmp);
		}
	    }
	    if(term.equals(TermBuilder.DF.tt())){
		throw new IllegalTacletException("There are some program schema" +
				" variables that can not be translated.");
	    }
	  
	}  
	// sixth step: quantify all free variables.
	term = quantifyTerm(term);
	

	// seventh step: translate the generics sorts.
	term = genericTranslator.translate(term, sorts, t, conditions,services);

	if(!checkForNotInstantiatedAttributes(term)){
	    throw new IllegalTacletException("There are some program schema " +
	    		"variables that can not be translated.\n /*The result: "+
	    		LogicPrinter.quickPrintTerm(term, services)+ "\n" +
	    		"Normally there are not enough attribute terms to instantiate" +
	    		"the taclet.*/");
	}
	

	term = translateRemainingNextToCreateAndCreates(term);
	
	
	

	
	
	
	TacletFormula tf = new DefaultTacletFormula(t, term, "",conditions);
	return tf;
    }
    
    
    private Term translateRemainingNextToCreateAndCreates(Term term){
	ImmutableArray<QuantifiableVariable> variables[] = new ImmutableArray[term
	                                                                      .arity()];
	Term[] subTerms = new Term[term.arity()];
	for (int i = 0; i < term.arity(); i++) {
	    variables[i] = term.varsBoundHere(i);
	    subTerms[i] = translateRemainingNextToCreateAndCreates(term.sub(i));
	    
	}
	
	if(AbstractTacletTranslator.isCreatedTerm(term, services)&&
	     !(term.sub(0).sort() instanceof GenericSort) ){
	   term= createCreatedTerm(term.sub(0), services);
	}else if(isNextToCreateTerm(term) &&
		!(term.sub(0).sort() instanceof GenericSort) ){
	    if(!(term.sub(0).sort() instanceof ObjectSort)){
	
	    }
	    
	    term.sub(0).sort();
	    term = createNextToCreateTerm((ObjectSort)term.sub(0).sort(), services);
	}else{
	    term = TermFactory.DEFAULT.createTerm(term.op(), subTerms, variables,
		        JavaBlock.EMPTY_JAVABLOCK);
	}
	return term;
    }
    
    /**
     * Checks whether the term is correctly instantiated.
     * @param term the term to be checked.
     * @return <code>true</code> if the term is instantiated, otherwise
     * <code>false</code>.
     */   
    private boolean checkForNotInstantiatedAttributes(Term term){
	/*if(term.op() instanceof MetaCreated){
	    return false;
	}*/
	if(term.op() instanceof AttributeOp){
	    AttributeOp op = (AttributeOp) term.op();
	    if(  op.sort().equals(ProgramSVSort.VARIABLE)){
		return false;
	    }

	}

	for (int i = 0; i < term.arity(); i++) {
	    if(!checkForNotInstantiatedAttributes(term.sub(i)))
		return false;

	}


	return true;
    }


    /**
     * Override this method to introduce a translating mechanism for taclets.
     * This mechanism should not translate generic types. This is done 
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
	       !(vc instanceof AbstractOrInterfaceType)&&
	       !(vc instanceof ArrayComponentTypeCondition)
	       )
	       {
		throw new IllegalTacletException(
			"The taclet has at least one variable condition" +
			" that is not supported: " + vc.toString()+": " +Taclet.class.getName()  );
	    }
	}
	

	/*if (t.varsNotFreeIn().hasNext()) {
	    throw new IllegalTacletException(
		    "The taclet has \\notFreeIn conditions.");
	}*/
	

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
	        || ((op instanceof SchemaVariableAdapter) && 
	        	((SchemaVariableAdapter) op).isVariableSV())
	        || ((op instanceof WarySubstOp))
	        || (op instanceof MetaNextToCreate)
	        || (op instanceof NonRigidHeapDependentFunction)
	        || (op instanceof AttributeOp)
	        || (op instanceof MetaCreated)
	        || (op instanceof ProgramSV)
	        || (op instanceof ArrayOp)
	   

	        
	

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
	
	term = tf.createTerm(term.op(), subTerms, variables,
		JavaBlock.EMPTY_JAVABLOCK);

	term = changeTerm(term);
	
	

	if(term.op() instanceof Quantifier){
	    // ImmutableArray<QuantifiableVariable> temp = new ImmutableArray<QuantifiableVariable>(); 
	    for(QuantifiableVariable qv : variables[0]){
		    for(TranslationListener l : listener){
			    l.eventQuantifiedVariable(qv);
			}
	    }	    
	}

	return term;
    }
    

    

   
    
    public LogicVariable getInstantiationOfLogicVar(Sort instantiation, LogicVariable lv){
	

	LogicVariable res = getLogicVariable(new Name(instantiation.name()
	        .toString()
	        + "__" + lv.name().toString()), instantiation);
	for (TranslationListener l : listener) {
	    l.eventSort(instantiation);
	}
	return res;
    }
    
 
    

    static public boolean isAbstractOrInterface(Sort sort){
        if(!isReferenceSort(sort)) return false;
             
        return    !(sort instanceof ArraySort) &&  
               ((ClassInstanceSort)sort).representAbstractClassOrInterface();
	
    }
    
    static public boolean isReferenceSort(Sort sort){
	return  ( sort instanceof ClassInstanceSort );
    }
    
    static public boolean isNextToCreateTerm(Term term){
	if(term.op() instanceof MetaNextToCreate){
	    return true;
	}
	return false;
    }
    
   
    
    /**
     * Quantifies a term, i.d. every free variable is bounded by a allquantor. 
     * @param term the term to be quantify.
     * @return the quantified term.
     */
     protected static Term quantifyTerm(Term term) throws IllegalTacletException{
	TermBuilder tb = TermBuilder.DF;
	// Quantify over all free variables.

	
	for (QuantifiableVariable qv : term.freeVars()) {
	  // if(!term.sort().equals(Sort.FORMULA)){
	    if(!(qv instanceof LogicVariable)){
		throw new IllegalTacletException("Error of translation: " +
				"There is a free variable that is not of type LogicVariable: "
			+ qv);
	    }

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
    public LogicVariable getLogicVariable(Name name, Sort sort) {
	name = new Name(eliminateSpecialChars(name.toString()));
	LogicVariable l = usedVariables.get(name.toString());
	if (l == null) {
	    
	    l = new LogicVariable(name, sort);
	    usedVariables.put(name.toString(), l);
	}
	return l;

    }
    
    /**
     * eliminates all special chars.
     * @param name
     * @return
     */
    static protected String eliminateSpecialChars(String name) {
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
	
	toReplace.add("#");
	replacement.add("_meta_");
	
	
	
	toReturn = removeIllegalChars(toReturn, toReplace, replacement);

	return toReturn.toString();
    }
    
    static  private StringBuffer removeIllegalChars(StringBuffer template, ArrayList<String> toReplace, ArrayList<String> replacement) {
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
    
    
    static public boolean isCreatedTerm(Term term, Services services){
	if(term.op() instanceof MetaCreated){
	    return true;
	}
	if(term.op() instanceof AttributeOp){
	    AttributeOp op = (AttributeOp) term.op();
	    if(op.sort().equals(ProgramSVSort.IMPLICITCREATED)){
		return true;
	    }
	    final KeYJavaType objectKJT = services.getJavaInfo().getJavaLangObject();
	    if(op.attribute().equals(
		    services.getJavaInfo().
		    getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, objectKJT))){
		return true;
	    }
		
	}
	return false;
    }
    
    /**
     * Creates the term <code>objectTerm</code>.created.
     * @param objectTerm
     * @param services
     * @return returns the created term.
     */
    static public Term createCreatedTerm(Term objectTerm,Services services) {
        JavaInfo javaInfo = services.getJavaInfo();
        ProgramVariable createdAttribute
                = javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED,
                                        javaInfo.getJavaLangObject());
        Term createdTerm = TermBuilder.DF.dot(objectTerm, createdAttribute);
        return createdTerm;
    }
    
    static public Term createNextToCreateTerm(ObjectSort sort, Services services){
	JavaInfo javaInfo = services.getJavaInfo();
	//javaInfo.getKeYJavaType(term)
	ProgramVariable createdAttribute
	         = javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE,
	                                     sort);
	
	Term createdTerm = TermFactory.DEFAULT.createVariableTerm(createdAttribute);
	return createdTerm;
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
	    }else //if(!(term.sort() instanceof GenericSort))
	    {
		term = tb.var(getLogicVariable(term.op().name(), term.sort()));
	
	    }
	    
	}
	
	if(term.op() instanceof Quantifier){
	    LinkedList<QuantifiableVariable> list = new LinkedList<QuantifiableVariable>();
	    
	    for(QuantifiableVariable qv : term.varsBoundHere(0)){
		list.add(getLogicVariable(qv.name(), qv.sort()));
	    }
	    
	    ImmutableArray<QuantifiableVariable> array = new ImmutableArray<QuantifiableVariable>(list);
	    term = TermFactory.DEFAULT.createQuantifierTerm((Quantifier)term.op(),array , term.sub(0));

	
	}
 


	return term;
    }
    
    

    
    public void addListener(TranslationListener listener){
	genericTranslator.addListener(listener);
	this.listener.add(listener);
    }
    
    public void removeListener(TranslationListener listener){
	genericTranslator.removeListener(listener);
	this.listener.remove(listener);
    }

    /**
     * @param t
     * @throws IllegalTacletException
     */
    protected abstract void check(Taclet t) throws IllegalTacletException;

}
