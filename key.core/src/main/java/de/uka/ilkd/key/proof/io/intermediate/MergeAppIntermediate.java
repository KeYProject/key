/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.axiom_abstraction.predicateabstraction.AbstractPredicateAbstractionLattice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;

/**
 * Encapsulates intermediate information for constructing a {@link MergeRule} application.
 *
 * @author Dominic Scheurer
 */
public class MergeAppIntermediate extends BuiltInAppIntermediate {

    private int id = 0;
    private final String mergeProc;
    private String distinguishingFormula = null;
    private int nrPartners = 0;
    private String abstractionPredicates = null;
    private String userChoices = null;
    private final Class<? extends AbstractPredicateAbstractionLattice> predAbstrLatticeType;

    /**
     * Constructs a new join rule.
     *
     * @param ruleName Name of the rule; should be "JoinRule".
     * @param pos Position information for the join rule application (Symbolic State - Program
     *        Counter formula).
     * @param id ID of the join rule application (should have been stored during proof saving and
     *        should match the joinNodeId fields of the corresponding partner nodes).
     * @param joinProc The name of the join procedure used during joining.
     * @param nrPartners Number of involved join partners.
     * @param newNames New names registered in the course of the join rule application.
     * @param distinguishingFormula The user-supplied distinguishing formula for the join.
     * @param predAbstrLatticeType The type for the used predicate abstraction lattice which
     *        determines how abstract domain elements are generated from predicates.
     * @param abstractionPredicates The abstraction predicates, if predicate abstraction is used as
     *        a join technique.
     * @param currAbstractionPredicates
     */
    public MergeAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos, int id,
            String joinProc, int nrPartners, ImmutableList<Name> newNames,
            String distinguishingFormula,
            Class<? extends AbstractPredicateAbstractionLattice> predAbstrLatticeType,
            String abstractionPredicates, String userChoices) {
        super(ruleName, pos, null, null, null, newNames);

        String mergeRuleName = MergeRule.INSTANCE.name().toString();
        assert ruleName.equals(mergeRuleName)
                : "This was somehow unexpected; are there other join rules than " + mergeRuleName
                    + "?";

        this.id = id;
        this.mergeProc = joinProc;
        this.nrPartners = nrPartners;
        this.distinguishingFormula = distinguishingFormula;
        this.abstractionPredicates = abstractionPredicates;
        this.predAbstrLatticeType = predAbstrLatticeType;
        this.userChoices = userChoices;
    }

    /**
     * @return ID of the join rule application (should have been stored during proof saving and
     *         should match the joinNodeId fields of the corresponding partner nodes).
     */
    public int getId() {
        return id;
    }

    /**
     * @return The name of the join procedure used during joining.
     */
    public String getJoinProc() {
        return mergeProc;
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
     * @return The abstraction predicates, if predicate abstraction is used as a join technique.
     */
    public Class<? extends AbstractPredicateAbstractionLattice> getPredAbstrLatticeType() {
        return predAbstrLatticeType;
    }

    /**
     * @return The abstraction predicates for predicate abstraction; null if none given.
     */
    public String getAbstractionPredicates() {
        return abstractionPredicates;
    }

    /**
     * @return The abstraction predicates for program variables involved in a join that are manually
     *         chosen by the user.
     */
    public String getUserChoices() {
        return userChoices;
    }

}
