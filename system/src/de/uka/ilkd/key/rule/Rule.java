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


/** this interface has to be implemented by all classes that want to
 * act as a rule in the calculus. */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;


public interface Rule {

    /** 
     * the rule is applied on the given goal using the
     * information of rule application. 
     * @param goal the Goal on which to apply <tt>ruleApp</tt>
     * @param services the Services with the necessary information
     * about the java programs 
     * @param ruleApp the rule application to be executed
     * @return all open goals below \old(goal.node()), i.e. the goals
     * resulting from the rule application
     * @throws Exception 
     */
    ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException;
    
    /** 
     * the name of the rule
     */
    Name name();

    /** 
     * returns the display name of the rule 
     */
    String displayName();

} 
