// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.SuccTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/** 
 * A SuccTaclet represents a taclet whose find part has to match a top level
 * formula in the succedent of the sequent. 
 */
public class SuccTaclet extends FindTaclet{

    private final boolean ignoreTopLevelUpdates;

     /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given
     * parameters that works on the succedent.  
     * @param name the name of the Taclet 
     * @param applPart contains the application part of an Taclet that is
     * the if-sequent, the variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param heuristics a list of heurisics for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * indicating a noninteractive or recursive use of the Taclet. 
     * @param find the find term of the Taclet
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the
     * prefix for each SchemaVariable in the Taclet
     */
    public SuccTaclet(Name name, TacletApplPart applPart,  
		    ImmutableList<TacletGoalTemplate> goalTemplates, 
		    ImmutableList<RuleSet> heuristics,
		    TacletAttributes attrs,
		    Term find,
                     boolean ignoreTopLevelUpdates,
		     ImmutableMap<SchemaVariable,TacletPrefix> prefixMap, ImmutableSet<Choice> choices){
	super(name, applPart, goalTemplates, heuristics, attrs,
	      find, prefixMap, choices);
        this.ignoreTopLevelUpdates = ignoreTopLevelUpdates;
	cacheMatchInfo();
    }	

    /** this method is used to determine if top level updates are
     * allowed to be ignored. This is the case if we have an Antec or
     * SuccTaclet but not for a RewriteTaclet
     * @return true if top level updates shall be ignored 
     */
    @Override
    protected boolean ignoreTopLevelUpdates() {
	return ignoreTopLevelUpdates;
    }

    /** CONSTRAINT NOT USED 
     * applies the replacewith part of Taclets
     * @param gt TacletGoalTemplate used to get the replaceexpression in the Taclet
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the taclet
     * @param posOfFind the PosInOccurrence belonging to the find expression
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, 
          SequentChangeInfo currentSequent,
          PosInOccurrence posOfFind,
          Services services,
          MatchConditions matchCond) {
       if (gt instanceof AntecSuccTacletGoalTemplate) {
          Sequent replWith = ((AntecSuccTacletGoalTemplate)gt).replaceWith();

          replaceAtPos(replWith.succedent(), currentSequent, posOfFind, services, matchCond);
          addToAntec(replWith.antecedent(), currentSequent, null, services, matchCond, posOfFind);	   	    	    
       } 
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * @param add the Sequent to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the taclet
     * @param posOfFind the PosInOccurrence describes the place where to add
     * the semisequent 
     * @param matchCond the MatchConditions with all required instantiations 
     */
    @Override
    protected void applyAdd(Sequent add, 
          SequentChangeInfo currentSequent,
          PosInOccurrence posOfFind,
          Services services,
          MatchConditions matchCond) {
       addToAntec(add.antecedent(), currentSequent, null, services, matchCond, posOfFind);
       addToSucc(add.succedent(), currentSequent, posOfFind, services, matchCond, posOfFind);
    }

    /** toString for the find part */
    StringBuffer toStringFind(StringBuffer sb) {
	return sb.append("\\find(==>").
	    append(find().toString()).append(")\n");
    }

    protected Taclet setName(String s) {
	SuccTacletBuilder b=new SuccTacletBuilder();
	b.setFind(find());
	return super.setName(s, b);
    }
}