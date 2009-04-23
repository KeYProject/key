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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.MapFromSchemaVariableToTacletPrefix;
import de.uka.ilkd.key.proof.Goal;

/** 
 * An AntecTaclet represents a taclet whose find part has to match a top level
 * formula in the antecedent of the sequent. 
 */
public class AntecTaclet extends FindTaclet{

     /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given
     * parameters.  
     * @param name the name of the Taclet 
     * @param applPart contains the application part of an Taclet that is
     * the if-sequent, the variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param heuristics a list of heurisics for the Taclet
     * @param constraint the Constraint under which the Taclet is valid
     * @param attrs attributes for the Taclet; these are boolean values
     * indicating a noninteractive or recursive use of the Taclet. 
     * @param find the find term of the Taclet
     * @param prefixMap a MapFromSchemaVariableToTacletPrefix that contains the
     * prefix for each SchemaVariable in the Taclet
     */
    public AntecTaclet(Name name, TacletApplPart applPart,  
		     ListOfTacletGoalTemplate goalTemplates, 
		     ListOfRuleSet heuristics,
		     Constraint constraint,
		     TacletAttributes attrs,
		     Term find, MapFromSchemaVariableToTacletPrefix prefixMap,
		     SetOfChoice choices){
	super(name, applPart, goalTemplates, heuristics, constraint, 
	      attrs, find, prefixMap, choices);
	cacheMatchInfo();
    }

   
    /** this method is used to determine if top level updates are
     * allowed to be ignored. This is the case if we have an Antec or
     * SuccTaclet but not for a RewriteTaclet
     * @return true if top level updates shall be ignored 
     */
    protected boolean ignoreTopLevelUpdates() {
	return true;
    }


    /** CONSTRAINT NOT USED 
     * applies the replacewith part of Taclets
     * @param gt TacletGoalTemplate used to get the replaceexpression in the Taclet
     * @param goal the Goal where the rule is applied
     * @param posOfFind the PosInOccurrence belonging to the find expression
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected void applyReplacewith(TacletGoalTemplate gt, Goal goal,
				    PosInOccurrence posOfFind,
				    Services services, 
				    MatchConditions matchCond) {
	if (gt instanceof AntecSuccTacletGoalTemplate) {
	    final Sequent replWith = ((AntecSuccTacletGoalTemplate)gt).replaceWith();

            if ( createCopies ( goal, posOfFind, matchCond ) ) {
                addToAntec ( replWith.antecedent (),
                             goal,
                             posOfFind,
                             services,
                             matchCond );
            } else {
                replaceAtPos ( replWith.antecedent (),
                               goal,
                               posOfFind,
                               services,
                               matchCond );
            }
	    addToSucc(replWith.succedent(), goal, 
		      null, services, matchCond);	   	    	    
	    
	
	} else {
	    // Then there was no replacewith...
	}
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * @param add the Sequent to be added
     * @param goal the Goal to be updated
     * @param posOfFind the PosInOccurrence describes the place where to add
     * the semisequent 
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected void applyAdd(Sequent add, Goal goal,
			    PosInOccurrence posOfFind,
			    Services services,
			    MatchConditions matchCond) {
	addToAntec(add.antecedent(), goal, posOfFind, services, matchCond);
	addToSucc(add.succedent(), goal, null, services, matchCond);
    }
        
    /** toString for the find part */
    StringBuffer toStringFind(StringBuffer sb) {
	return sb.append("\\find(").
	    append(find().toString()).append("==>)\n");
    }

    protected Taclet setName(String s) {
	AntecTacletBuilder b=new AntecTacletBuilder();
	b.setFind(find());
	return super.setName(s, b);
    }

  
}
