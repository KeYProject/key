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

package de.uka.ilkd.key.rule.label;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Name;

/**
 * Instances of this class provides functionality only if a supported
 * rule is active.
 * @author Martin Hentschel
 * @see ChildTermLabelPolicy
 * @see TermLabelUpdate
 * @see TermLabelRefactoring
 */
public interface RuleSpecificTask {
   /**
    * Returns the supported rule {@link Name}s or {@code null} or an empty
    * list if all rules are supported.
    * @return The list of supported rule {@link Name}s or {@code null}/empty list if all rules are supported.
    */
   public ImmutableList<Name> getSupportedRuleNames();
}