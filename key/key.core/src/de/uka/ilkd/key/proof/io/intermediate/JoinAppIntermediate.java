// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates intermediate information for constructing a join rule
 * application.
 *
 * @author Dominic Scheurer
 */
public class JoinAppIntermediate extends BuiltInAppIntermediate {

    private int id = 0;
    private String joinProc = null;
    private String distinguishingFormula = null;
    private int nrPartners = 0;
    private ImmutableList<Pair<String, String>> abstractionPredicates;
    private Class<? extends AbstractPredicateAbstractionLattice> predAbstrLatticeType;

    /**
     * Constructs a new join rule.
     *
     * @param ruleName
     *            Name of the rule; should be "JoinRule".
     * @param pos
     *            Position information for the join rule application (Symbolic
     *            State - Program Counter formula).
     * @param id
     *            ID of the join rule application (should have been stored
     *            during proof saving and should match the joinNodeId fields of
     *            the corresponding partner nodes).
     * @param joinProc
     *            The name of the join procedure used during joining.
     * @param nrPartners
     *            Number of involved join partners.
     * @param newNames
     *            New names registered in the course of the join rule
     *            application.
     * @param distinguishingFormula
     *            The user-supplied distinguishing formula for the join.
     * @param predAbstrLatticeType
     *            The type for the used predicate abstraction lattice which
     *            determines how abstract domain elements are generated from
     *            predicates.
     * @param abstractionPredicates
     *            The abstraction predicates, if predicate abstraction is used
     *            as a join technique.
     * @param currAbstractionPredicates
     */
    public JoinAppIntermediate(
            String ruleName,
            Pair<Integer, PosInTerm> pos,
            int id,
            String joinProc,
            int nrPartners,
            ImmutableList<Name> newNames,
            String distinguishingFormula,
            Class<? extends AbstractPredicateAbstractionLattice> predAbstrLatticeType,
            ImmutableList<Pair<String, String>> abstractionPredicates) {
        super(ruleName, pos, null, null, newNames);

        assert ruleName.equals("JoinRule") : "This was somehow unexpected; are there other join rules than JoinRule?";

        this.id = id;
        this.joinProc = joinProc;
        this.nrPartners = nrPartners;
        this.distinguishingFormula = distinguishingFormula;
        this.abstractionPredicates = abstractionPredicates;
        this.predAbstrLatticeType = predAbstrLatticeType;
    }

    /**
     * @return ID of the join rule application (should have been stored during
     *         proof saving and should match the joinNodeId fields of the
     *         corresponding partner nodes).
     */
    public int getId() {
        return id;
    }

    /**
     * @return The name of the join procedure used during joining.
     */
    public String getJoinProc() {
        return joinProc;
    }

    /**
     * @return Number of involved join partners.
     */
    public int getNrPartners() {
        return nrPartners;
    }

    /**
     * @return The user-supplied distinguishing formula; null if none given.
     */
    public String getDistinguishingFormula() {
        return distinguishingFormula;
    }

    /**
     * @return The abstraction predicates, if predicate abstraction is used as a
     *         join technique.
     */
    public Class<? extends AbstractPredicateAbstractionLattice> getPredAbstrLatticeType() {
        return predAbstrLatticeType;
    }

    /**
     * @return The abstraction predicates for predicate abstraction; null if
     *         none given.
     */
    public ImmutableList<Pair<String, String>> getAbstractionPredicates() {
        return abstractionPredicates;
    }

}
