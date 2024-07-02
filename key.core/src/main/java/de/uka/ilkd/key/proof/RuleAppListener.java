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

package de.uka.ilkd.key.proof;

/**
 * This listener is notified whenever a rule is applied in an ongoing proof.
 */
@FunctionalInterface
public interface RuleAppListener {

    /**
     * Invoked when a rule has been applied.
     *
     * @param e the proof event containing the rule application.
     */
    void ruleApplied(de.uka.ilkd.key.proof.ProofEvent e);
}