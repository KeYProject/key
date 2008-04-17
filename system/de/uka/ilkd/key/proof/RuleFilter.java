// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.Rule;

/**
 * Interface for objects that represent sets of rules, and which can be used
 * to distinguish different kinds of rules.
 */
public interface RuleFilter {
    
    boolean filter ( Rule rule );

}
