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

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.executor.javadl.NoFindTacletExecutor;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

/** 
 * Used to implement a Taclet that has no <I>find</I> part. This kind of taclet
 * is not attached to term or formula, but to a complete sequent. A typical
 * representant is the <code>cut</code> rule. 
 */
public class NoFindTaclet extends Taclet {

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given
     * parameters.  
     * @param name the name of the Taclet 
     * @param applPart contains the application part of an Taclet that is
     * the if-sequent, the variable conditions
     * @param goalTemplates the IList<TacletGoalTemplate> containg all goal descriptions of the taclet to be created
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the
     * prefix for each SchemaVariable in the Taclet
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public NoFindTaclet(Name name, TacletApplPart applPart,  
            ImmutableList<TacletGoalTemplate> goalTemplates, 
            ImmutableList<RuleSet> ruleSets, 
            TacletAttributes attrs,
            ImmutableMap<SchemaVariable,TacletPrefix> prefixMap,
            ImmutableSet<Choice> choices){
        super(name, applPart, goalTemplates, ruleSets, attrs, prefixMap, 
                choices);
        createTacletServices();
    } 

    @Override
    protected void createAndInitializeExecutor() {
        executor = new NoFindTacletExecutor(this);
    }

    /**
     * @return Set of schemavariables of the if and the (optional)
     * find part
     */
    public ImmutableSet<SchemaVariable> getIfFindVariables () {
        return getIfVariables ();
    }

    /**
     * the empty set as a no find taclet has no other entities where 
     * variables cann occur bound than in the goal templates
     * @return empty set
     */
    protected ImmutableSet<QuantifiableVariable> getBoundVariablesHelper() {        
        return DefaultImmutableSet.<QuantifiableVariable>nil();
    }

    @Override
    public NoFindTaclet setName(String s) {        
        final TacletApplPart applPart = 
                new TacletApplPart(ifSequent(), varsNew(), varsNotFreeIn(), 
                varsNewDependingOn(), getVariableConditions());
        final TacletAttributes attrs = new TacletAttributes();
        attrs.setDisplayName(displayName());
        
        return new NoFindTaclet(new Name(s), 
                applPart, goalTemplates(), getRuleSets(), attrs, prefixMap, choices);
    }

    
}