// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import java.util.HashMap;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/** subclasss build Schematic Theory Specific Rules (Taclets) */
public abstract class TacletBuilder {

    protected final static Name NONAME = new Name("unnamed");

    protected Taclet taclet;

    protected Name name                     = NONAME;
    protected Sequent ifseq                 = Sequent.EMPTY_SEQUENT; 
    protected ListOfNewVarcond varsNew      = SLListOfNewVarcond.EMPTY_LIST;
    protected ListOfNotFreeIn varsNotFreeIn = SLListOfNotFreeIn.EMPTY_LIST;
    protected ListOfNewDependingOn varsNewDependingOn =
	SLListOfNewDependingOn.EMPTY_LIST;
    protected ListOfTacletGoalTemplate goals= SLListOfTacletGoalTemplate.EMPTY_LIST;
    protected ListOfRuleSet ruleSets    = SLListOfRuleSet.EMPTY_LIST;
    protected TacletAttributes attrs        = new TacletAttributes(); 
    protected Constraint constraint         = Constraint.BOTTOM;
    /** List of additional generic conditions on the instantiations of
     * schema variables. */
    protected ListOfVariableCondition variableConditions       = SLListOfVariableCondition.EMPTY_LIST; 
    protected HashMap<TacletGoalTemplate, SetOfChoice> goal2Choices          = null;
    protected SetOfChoice choices           = SetAsListOfChoice.EMPTY_SET;


    private static boolean containsFreeVarSV(Term t) {
	for (final QuantifiableVariable var : t.freeVars()) {
	    if (var instanceof SchemaVariable && 
		((SchemaVariable)var).isVariableSV()) {
		return true;
	    }
	}
	return false;
    }

    private static boolean containsFreeVarSV(Sequent sequent) {
	for (final ConstrainedFormula cf : sequent) {
	    if (containsFreeVarSV(cf.formula())) {
		return true;
	    }
	}
	return false;
    }

    static void checkContainsFreeVarSV(Sequent seq, Name tacletName, 
            String str) {
	if (containsFreeVarSV(seq)) {
	    throw new TacletBuilderException(tacletName, 
                       "Free Variable in " + str
                       + " in Taclet / sequent: "+seq);
	}
    }

    static void checkContainsFreeVarSV(Term t, Name tacletName, String str) {
	if (containsFreeVarSV(t)) {
	    throw new TacletBuilderException(tacletName, 
                    "Free Variable found in "
	            +str+" in Taclet / Term: "+t);
	}
    }



    /** 
     * returns the name of the Taclet to be built
     */
    public Name getName(){
	return this.name;
    }


    /** sets the name of the Taclet to be built
     */
    public void setName(Name name){
	this.name=name;
    }

    /** sets an optional display name (presented to the user)
     */
    public void setDisplayName(String s) {
       attrs.setDisplayName(s);
    }

    /** adds an old name to the list of old names
     */
    public void addOldName(String s) {
       attrs.addOldName(s);
    }


    public void setHelpText(String s) {
       attrs.setHelpText(s);
    }

    /** sets the ifseq of the Taclet to be built
     */
    public void setIfSequent(Sequent seq){
	checkContainsFreeVarSV(seq, getName(), "sequent");	
	this.ifseq=seq;
    }
    
    /** sets the constraint that has to be satisfied if the Taclet
     * should be valid */
    public void setConstraint(Constraint constraint) {
	this.constraint=constraint;
    }

    /**
     * adds a mapping from GoalTemplate <code>gt</code> to SetOfChoice 
     * <code>soc</code>
     */
    public void addGoal2ChoicesMapping(TacletGoalTemplate gt, SetOfChoice soc){
	if(goal2Choices==null){
	    goal2Choices = new HashMap<TacletGoalTemplate, SetOfChoice>();
	}
	goal2Choices.put(gt, soc);
    }
	
    public HashMap<TacletGoalTemplate, SetOfChoice> getGoal2Choices(){
	return goal2Choices;
    }

    public void setChoices(SetOfChoice choices){
	this.choices = choices;
    }

    public SetOfChoice getChoices(){
	return choices;
    }

    /** adds a new <I>new</I> variable to the variable conditions of
     * the Taclet: v is new and has the sort as asSort if elementsort=false and the
     * sort of the elements of asSort if elementsort=true and asSort is a program
     * array SV. 
     */
    public void addVarsNew(SchemaVariable v, 
            SchemaVariable asSort, boolean elementsort){
	addVarsNew(new NewVarcond(v, asSort, elementsort));
    }
    
    /** adds a new <I>new</I> variable to the variable conditions of
     * the Taclet: v is new and has the sort as asSort
     */
    public void addVarsNew(SchemaVariable v, SchemaVariable asSort){
	addVarsNew(new NewVarcond(v, asSort));
    }

    /** adds a new <I>new</I> variable to the variable conditions of
     * the Taclet: v is new and has type sort
     */
    public void addVarsNew(SchemaVariable v, Sort sort){
	addVarsNew(new NewVarcond(v, sort));
    }

    /** adds a new <I>new</I> variable to the variable conditions of
     * the Taclet: v is new.
     */
    public void addVarsNew(NewVarcond nv){
	if (!nv.getSchemaVariable().isProgramSV()) {
	    throw new TacletBuilderException(this, 
                    "Tried to add condition:"+nv+ 
                    "to new vars-list. That can"+ 
                    "match more than program"
                    +" variables.");
	} 
	varsNew = varsNew.prepend(nv);
    }
    
    /** adds a list of <I>new</I> variables to the variable conditions of
     * the Taclet: v is new for all v's in the given list
     */
    public void addVarsNew(ListOfNewVarcond list) {	
	IteratorOfNewVarcond it = list.iterator();
	while (it.hasNext()) {
	    addVarsNew(it.next());
	}
    }

    /** adds a new <I>NotFreeIn</I> variable pair to the variable conditions of
     * the Taclet: v0 is not free in v1.
     */
    public void addVarsNotFreeIn(SchemaVariable v0, SchemaVariable v1){
	varsNotFreeIn = varsNotFreeIn.prepend(new NotFreeIn(v0, v1));
    }

   /** adds a list of <I>NotFreeIn</I> variable pairs to the variable 
    *conditions of
    * the Taclet: v0 is not free in v1 for all entries (v0,v1) in the given list.
    */
    public void addVarsNotFreeIn(ListOfNotFreeIn list){	
	varsNotFreeIn=varsNotFreeIn.prepend(list);
    }


    /**
     * Add a "v0 depending on v1"-statement. "v0" may not occur within
     * the if sequent or the find formula/term, however, this is not
     * checked
     */
    public void addVarsNewDependingOn(SchemaVariable v0, SchemaVariable v1){	
	varsNewDependingOn=varsNewDependingOn.prepend
	    ( new NewDependingOn ( v0, v1 ) );
    }



    /** Add an additional generic condition on the instatiation of
     * schema variables. */
    public void addVariableCondition(VariableCondition vc) {
	variableConditions = variableConditions.append(vc);
    }
    

    /** adds a new goal descriptions to the goal descriptions of the Taclet.
     * The TacletGoalTemplate must be of 
     * the appropriate kind (Rewrite/Ante/Succ),
     * otherwise an IllegalArgumentException is thrown.
     */
    public abstract void addTacletGoalTemplate(TacletGoalTemplate goal);
  

    /** adds a new rule set to the rule sets of the Taclet.
     */
    public void addRuleSet(RuleSet rs) {
	ruleSets = ruleSets.prepend(rs);
    }

    public void setRuleSets(ListOfRuleSet rs) {
	ruleSets = rs;
    }

    /** sets the noninteractive flag to the given value.
     */
    public void setNoninteractive(boolean ni) {
	attrs.setNoninteractive(ni);
    }


    public Sequent ifSequent() {
	return ifseq;
    }

    public ListOfTacletGoalTemplate goalTemplates() {
	return goals;
    }

    public IteratorOfNotFreeIn varsNotFreeIn() {
	return varsNotFreeIn.iterator();
    }

    public void setTacletGoalTemplates(ListOfTacletGoalTemplate g) {
	goals=g;
    }

    /** builds and returns the Taclet that is specified by
     * former set... / add... methods. If no name is specified then
     * an Taclet with an empty string name is build. No specifications
     * for variable conditions, goals or rule sets imply that the
     * corresponding parts of the Taclet are empty. No specification for
     * the if-sequence is represented as a sequent with two empty
     * semisequences. No specification for the interactive or
     * recursive flags imply that the flags are not set. 
     * No specified find part for Taclets that require a find part
     * causes an IllegalStateException. 
     */
    public abstract Taclet getTaclet();

    public Taclet getTacletWithoutInactiveGoalTemplates(SetOfChoice active){
	if(goal2Choices==null || goals.isEmpty()){
	    return getTaclet();
	}else{
	    ListOfTacletGoalTemplate oldGoals = goals;
	    IteratorOfTacletGoalTemplate it = oldGoals.iterator();
	    Taclet result;
	    while(it.hasNext()){
		TacletGoalTemplate goal = it.next();
		if(goal2Choices.get(goal) != null && 
		   !goal2Choices.get(goal).subset(active)){
		    goals = goals.removeAll(goal);
		}
	    }
	    if(goals.isEmpty()){
		result = null;
	    }else{
		result = getTaclet();
	    }
	    goals = oldGoals;
	    return result;
	}
    }

    static class TacletBuilderException extends IllegalArgumentException {
	
      
        private Name tacletname;
        private String errorMessage;
                
        TacletBuilderException(Name tacletname, 
                String errorMessage) {
            this.tacletname = tacletname;
            this.errorMessage = errorMessage;
        }
        
        TacletBuilderException(TacletBuilder tb,  String errorMessage) {
           this(tb.getName(), errorMessage);
        }
        
        
        public String getMessage() {
            String message = (tacletname == null ? 
                    "(unknown taclet name)" : tacletname.toString());
            return  message + ": " + errorMessage; 
        }
        
    }
    
}
