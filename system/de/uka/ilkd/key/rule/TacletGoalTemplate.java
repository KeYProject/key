// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.*;

/** 
 * this class contains the goals of the schematic theory specific
 * rules (Taclet). There are new sequents that have to be added, new
 * rules and rule variables. The replacewith-goal is implemented in
 * subclasses 
 */
public class TacletGoalTemplate {

    /** stores sequent that is one of the new goals */
    private Sequent addedSeq = Sequent.EMPTY_SEQUENT;     

    /** stores list of Taclet which are introduced*/
    private ListOfTaclet addedRules = SLListOfTaclet.EMPTY_LIST;

    /** program variables added by this taclet to the namespace */
    private SetOfSchemaVariable addedProgVars
	= SetAsListOfSchemaVariable.EMPTY_SET;
        
    private String name = null;
        

    /** creates new Goaldescription 
     *@param addedSeq new Sequent to be added
     *@param addedRules ListOfTaclet contains the new allowed rules
     * at this branch 
     *@param addedProgVars a SetOfSchemaVariable which will be instantiated with
     * a application time unused (new) program variables that are introduced by 
     * an application of this template
     */
    public TacletGoalTemplate(Sequent addedSeq,
			      ListOfTaclet addedRules,
			      SetOfSchemaVariable addedProgVars) {
	TacletBuilder.checkContainsFreeVarSV(addedSeq, null, "add sequent");
	   
	this.addedRules=addedRules;	
	this.addedSeq=addedSeq;
	this.addedProgVars = addedProgVars;
    }
    
    /** 
     * creates new Goaldescription
     * same effect as <code>new TacletGoalTemplate(addedSeq, 
     *                                             addedRules,
     *                                             SetAsListOfSchemaVariable.EMPTY_SET)
     *                                             </code>
     *                                               
     * @param addedSeq new Sequent to be added
     * @param addedRules ListOfTaclet contains the new allowed rules
     *  at this branch
     */ 
    public TacletGoalTemplate(Sequent addedSeq,
			      ListOfTaclet addedRules) {		
	this(addedSeq, addedRules, SetAsListOfSchemaVariable.EMPTY_SET);
    }


    /** a Taclet may replace parts of sequent.
     * @return term (or sequent) to be placed instead of the findexp-term.
     * REMARK: returns 'null' if there is no replace-with part !
     * Overwritten in subclasses !
     */
    Object replaceWithExpressionAsObject() {
	return null;
    }


    /** a Taclet may add a new Sequent as Goal. Use this method to get
     * this Sequent
     * @return Sequent to be added as Goal or Sequent.EMPTY_SEQUENT if
     * no such Sequent exists
     */
    public Sequent sequent() {
	return addedSeq;
    }

    /** the goal of a Taclet may introduce new rules. Call this method
     * to get them 
     * @return ListOfTaclet contains new introduced rules
     */
    public ListOfTaclet rules() {
	return addedRules;
    }

   
    /** returns the set of schemavaroable whos einstantiations will be
     * added to the sequent namespace */
    public SetOfSchemaVariable addedProgVars() {
	return addedProgVars;
    }


    /**
     * rertieves and returns all variables that are bound in the 
     * goal template
     * @return all variables that occur bound in this goal template
     */
    protected SetOfQuantifiableVariable getBoundVariables() {
	SetOfQuantifiableVariable result
	    =SetAsListOfQuantifiableVariable.EMPTY_SET;
	
        final IteratorOfTaclet tacletIt=rules().iterator();
	
        while (tacletIt.hasNext()) {
	    result=result.union(tacletIt.next().getBoundVariables());
	}	    
	
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(sequent());
        
        return result.union(bvv.getBoundVariables());	 
    }
    
    
    public void setName(String s) {
       name = s;
    }
    
    public String name() {
       return name;
    }

    public boolean equals(Object o) {
	if ( ! ( o instanceof TacletGoalTemplate ) )
	    return false;

	TacletGoalTemplate other = (TacletGoalTemplate) o;
	
	return 
	    addedSeq.equals(other.addedSeq)
	    && addedRules.equals(other.addedRules);
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + addedSeq.hashCode();
    	result = 37 * result + addedRules.hashCode();    	
    	return result;
    }

    
    /** toString */
    public String toString() {
	String result="";
	if (sequent()!=Sequent.EMPTY_SEQUENT) result+="\\add "+sequent()+" "; 
	if (rules()!=SLListOfTaclet.EMPTY_LIST) result+="\\addrules "+rules()+" ";
	if (addedProgVars().size()>0) result+="\\addprogvars "+addedProgVars()+" ";	
	return result;
    }

}
