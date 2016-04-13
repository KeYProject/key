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

package de.uka.ilkd.key.proof.join;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;

/**
 * Methods for checking the applicability of a join for a given selection
 * and thereby computing the prospective join partners.
 *
 * @see JoinProcessor
 * @author Benjamin Niedermann
 */
public class JoinIsApplicable {
    public static final JoinIsApplicable INSTANCE = new JoinIsApplicable();

    private JoinIsApplicable() {
        /* It's a singleton */
    }

    /**
     * @param goal
     *            The goal to join.
     * @param pio
     *            Selected formula (symblic state - program counter part) for
     *            the join.
     * @return The list of possible join partner objects -- may be empty (then,
     *         the join is not applicable).
     */
    public List<ProspectivePartner> isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return new LinkedList<ProspectivePartner>();
        }
        return computeProspecitvePartner(goal, pio);
    }

    /**
     * Computes the partners for the given selection.
     *
     * @param goal
     *            Goal which should be joined.
     * @param pio
     *            Selected formula (symblic state - program counter part) for
     *            the join.
     * @return The list of possible join partners.
     */
    public List<ProspectivePartner> computeProspecitvePartner(Goal goal,
            PosInOccurrence pio) {
        assert !pio.isInAntec();
        List<ProspectivePartner> partners = new LinkedList<ProspectivePartner>();

        for (Goal g2 : goal.proof().openGoals()) {
            if (g2 != goal) {
                ProspectivePartner pair = areProspectivePartners(goal, pio, g2);
                if (pair != null) {
                    partners.add(pair);
                }
            }
        }

        return partners;
    }

    /**
     * Checks if two given goals are possible join partners for a given selected
     * sequent formula (defined by pio); returns a ProspectivePartner object if
     * this is the case and null otherwise.
     *
     * @param g1
     *            Goal for the first node to join.
     * @param pio
     *            Selected formula (symbolic state - program counter part) for
     *            the join.
     * @param g2
     *            Second goal for the join.
     * @return A ProspectivePartner object if the given goals may be joined or
     *         null otherwise.
     */
    private ProspectivePartner areProspectivePartners(Goal g1,
            PosInOccurrence pio, Goal g2) {
        Term referenceFormula = pio.subTerm();

        assert g1.proof().getServices() == g2.proof().getServices();
        TermBuilder tb = g1.proof().getServices().getTermBuilder();

        Term update1 = referenceFormula.op() instanceof UpdateApplication ? referenceFormula
                .sub(0) : tb.skip();

        referenceFormula = referenceFormula.op() instanceof UpdateApplication ? referenceFormula
                .sub(1) : referenceFormula;

        for (SequentFormula sf : g2.sequent().succedent()) {
            Term formula = sf.formula();
            Term update2 = tb.skip();
            if (formula.op() instanceof UpdateApplication
                    && !formula.equalsModRenaming(referenceFormula)) {
                update2 = formula.sub(0);// don't change the order of this and
                                         // the following line.
                formula = formula.sub(1);

            }
            if (formula.equalsModRenaming(referenceFormula)) {
                return new ProspectivePartner(referenceFormula, g1.node(),
                        pio.sequentFormula(), update1, g2.node(), sf,
                        update2);
            }
        }
        return null;
    }

}