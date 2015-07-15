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

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.executor.javadl.AntecTacletExecutor;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/** 
 * An AntecTaclet represents a taclet whose find part has to match a top level
 * formula in the antecedent of the sequent. 
 */
public class AntecTaclet extends FindTaclet{

    private final boolean ignoreTopLevelUpdates;

     /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given
     * parameters.  
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
    public AntecTaclet(Name name, TacletApplPart applPart,  
		     ImmutableList<TacletGoalTemplate> goalTemplates, 
		     ImmutableList<RuleSet> heuristics,
		     TacletAttributes attrs,
		     Term find,
                     boolean ignoreTopLevelUpdates,
		     ImmutableMap<SchemaVariable,TacletPrefix> prefixMap, ImmutableSet<Choice> choices,
		     ImmutableSet<TacletAnnotation> tacletAnnotations){
        super(name, applPart, goalTemplates, heuristics, attrs, 
                find, prefixMap, choices, tacletAnnotations);
        this.ignoreTopLevelUpdates = ignoreTopLevelUpdates;
        createTacletServices();
    }

   
    /** this method is used to determine if top level updates are
     * allowed to be ignored. This may be the case if we have an Antec or
     * SuccTaclet but not for a RewriteTaclet
     * @return true if top level updates shall be ignored 
     */
    @Override
    public boolean ignoreTopLevelUpdates() {
	return ignoreTopLevelUpdates;
    }


        
    /** toString for the find part */
    protected StringBuffer toStringFind(StringBuffer sb) {
	return sb.append("\\find(").
	    append(find().toString()).append("==>)\n");
    }


    @Override
    protected void createAndInitializeExecutor() {
        executor = new AntecTacletExecutor<AntecTaclet>(this);
    }

    @Override
    public AntecTaclet setName(String s) {        
        final TacletApplPart applPart = 
                new TacletApplPart(ifSequent(), varsNew(), varsNotFreeIn(), 
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes();
        attrs.setDisplayName(displayName());
        
        return new AntecTaclet(new Name(s), 
                applPart, goalTemplates(), getRuleSets(), attrs, find, ignoreTopLevelUpdates, prefixMap, choices, tacletAnnotations);
    }
}