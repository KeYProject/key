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

package de.uka.ilkd.key.strategy.feature.instantiator;

import java.util.Iterator;

import de.uka.ilkd.key.rule.RuleApp;

/**
 * Interface encapsulating points during the evaluation of a feature term where
 * it is either possible to take different branches, or where the feature has to
 * change the rule application in question (e.g. by instantiation schema
 * variables).
 */
public interface ChoicePoint {

    /**
     * Obtain the branches that can be taken at this point.
     * 
     * @param oldApp
     *            the current rule application, which can already have been
     *            modified by earlier <code>ChoicePoint</code>s
     * @return an iterator over the branches of the <code>ChoicePoint</code>
     */
    Iterator<CPBranch> getBranches(RuleApp oldApp);

}