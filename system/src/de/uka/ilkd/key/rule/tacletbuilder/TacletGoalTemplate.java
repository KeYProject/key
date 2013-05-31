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


package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;

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
    private ImmutableList<Taclet> addedRules = ImmutableSLList.<Taclet>nil();

    /** program variables added by this taclet to the namespace */
    private ImmutableSet<SchemaVariable> addedProgVars
	= DefaultImmutableSet.<SchemaVariable>nil();
        
    private String name = null;
        

    /** creates new Goaldescription 
     *@param addedSeq new Sequent to be added
     *@param addedRules IList<Taclet> contains the new allowed rules
     * at this branch 
     *@param addedProgVars a SetOf<SchemaVariable> which will be instantiated with
     * a application time unused (new) program variables that are introduced by 
     * an application of this template
     */
    public TacletGoalTemplate(Sequent addedSeq,
			      ImmutableList<Taclet> addedRules,
			      ImmutableSet<SchemaVariable> addedProgVars) {
	TacletBuilder.checkContainsFreeVarSV(addedSeq, null, "add sequent");
	   
	this.addedRules = addedRules;	
	this.addedSeq = addedSeq;
	this.addedProgVars = addedProgVars;
    }
    
    /** 
     * creates new Goaldescription
     * same effect as <code>new TacletGoalTemplate(addedSeq, 
     *                                             addedRules,
     *                                             SetAsListOf.<SchemaVariable>nil())
     *                                             </code>
     *                                               
     * @param addedSeq new Sequent to be added
     * @param addedRules IList<Taclet> contains the new allowed rules
     *  at this branch
     */ 
    public TacletGoalTemplate(Sequent addedSeq,
			      ImmutableList<Taclet> addedRules) {		
	this(addedSeq, addedRules, DefaultImmutableSet.<SchemaVariable>nil());
    }


    /** a Taclet may replace parts of sequent.
     * @return term (or sequent) to be placed instead of the findexp-term.
     * REMARK: returns 'null' if there is no replace-with part !
     * Overwritten in subclasses !
     */
    public Object replaceWithExpressionAsObject() {
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
     * @return IList<Taclet> contains new introduced rules
     */
    public ImmutableList<Taclet> rules() {
	return addedRules;
    }

   
    /** returns the set of schemavaroable whose instantiations will be
     * added to the sequent namespace */
    public ImmutableSet<SchemaVariable> addedProgVars() {
	return addedProgVars;
    }


    /**
     * retrieves and returns all variables that are bound in the 
     * goal template
     * @return all variables that occur bound in this goal template
     */
    public ImmutableSet<QuantifiableVariable> getBoundVariables() {
	ImmutableSet<QuantifiableVariable> result
	    = DefaultImmutableSet.<QuantifiableVariable>nil();

        for (Taclet taclet : rules()) {
            result = result.union(taclet.getBoundVariables());
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

    
    @Override    
    public boolean equals(Object o) {
	if ( ! ( o instanceof TacletGoalTemplate ) )
	    return false;

	TacletGoalTemplate other = (TacletGoalTemplate) o;
	
	return 
	    addedSeq.equals(other.addedSeq)
	    && addedRules.equals(other.addedRules);
    }


    @Override    
    public int hashCode() {
    	int result = 17;
    	result = 37 * result + addedSeq.hashCode();
    	result = 37 * result + addedRules.hashCode();    	
    	return result;
    }

    
    @Override
    public String toString() {
	String result="";
	if (!sequent().isEmpty()) result+="\\add "+sequent()+" "; 
	if (!rules().isEmpty()) result+="\\addrules "+rules()+" ";
	if (!addedProgVars().isEmpty()) result+="\\addprogvars "+addedProgVars()+" ";	
	return result;
    }
}
