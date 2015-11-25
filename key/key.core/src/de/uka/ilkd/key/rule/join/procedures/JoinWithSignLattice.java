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

package de.uka.ilkd.key.rule.join.procedures;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.boollattice.BooleanLattice;
import de.uka.ilkd.key.axiom_abstraction.signanalysis.SignAnalysisLattice;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Rule that joins two sequents based on a sign lattice for integers. Boolean
 * variables are joined with a simple lattice for booleans. Program variables of
 * other types than int and boolean are unchanged if they are equal in both
 * states and set to fresh variables if they have different values.
 * 
 * @deprecated You should use {@link JoinWithPredicateAbstraction} instead.
 * @author Dominic Scheurer
 */
public class JoinWithSignLattice extends JoinWithLatticeAbstraction {

    private static JoinWithSignLattice INSTANCE = null;

    public static JoinWithSignLattice instance() {
        if (INSTANCE == null) {
            INSTANCE = new JoinWithSignLattice();
        }
        return INSTANCE;
    }

    private static final String DISPLAY_NAME = "JoinBySignLatticeAbstraction";

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.rule.join.JoinProcedure#complete()
     */
    @Override
    public boolean complete() {
        return true;
    }

    @Override
    protected AbstractDomainLattice getAbstractDomainForSort(Sort s,
            Services services) {
        final Sort intSort =
                (Sort) services.getNamespaces().sorts().lookup(new Name("int"));
        final Sort booleanSort =
                (Sort) services.getNamespaces().sorts()
                        .lookup(new Name("boolean"));

        if (s.equals(intSort)) {
            return SignAnalysisLattice.getInstance();
        }
        else if (s.equals(booleanSort)) {
            return BooleanLattice.getInstance();
        }
        else {
            return null;
        }
    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }
}
