// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
/*
 * Created on 16.12.2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

/**
 * @author bubel
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public interface IUpdateRule {
    /**
     * Determines whether this rule is applicable for the pair of update and
     * target (the term on which the update will be applied) term
     * 
     * @param update
     *            the Update to be applied on the given term
     * @param target
     *            the Term on which the update is applied
     * @return true if the rule can be applied on the update, target pair
     */
    public abstract boolean isApplicable(Update update, Term target);

    /**
     * Applies the update on the target term. This method must only be called if
     * <code>isApplicable</code> returns <code>true</code> for this
     * combination of update and target
     * 
     * @param update
     *            the Update to be applied on target
     * @param target
     *            the Term on which the update is applied
     * @param services
     *            the Services object
     * @return the Term resulting from the update on the target
     */
    public abstract Term apply(Update update, Term target, Services services);
    
    /**
     * Derive a formula that describes in which cases the top-level operator
     * (location) described by <code>target</code> is updated by the given
     * update. This method must only be called if <code>isApplicable</code>
     * returns <code>true</code> for this combination of update and target
     * 
     * @param update
     *            the modification of function interpretations that is
     *            considered
     * @param target
     *            description of the location we are interested in;
     *            precondition: <code>target.op() instanceof Location</code>
     * @param services
     *            the Services object
     * @return formula that evaluates to <tt>true</tt> iff <code>update</code>
     *         evaluates to a semantic update that affects the location
     *         described by <code>target</code>
     */
    public abstract Term matchingCondition(Update update, 
	    				   Term target, 
	    				   Services services);
}
