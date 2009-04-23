// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** this interface has to be implemented by all classes that want to
 * act as a rule in the calculus. */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;


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
     */
    ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp);
    
    /** 
     * the name of the rule
     */
    Name name();

    /** 
     * returns the display name of the rule 
     */
    String displayName();

} 
