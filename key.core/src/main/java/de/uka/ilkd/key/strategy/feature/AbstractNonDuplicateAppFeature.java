/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.*;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.rules.instantiation.InstantiationEntry;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;


public abstract class AbstractNonDuplicateAppFeature extends BinaryTacletAppFeature {
    protected AbstractNonDuplicateAppFeature() {}

    /**
     * Compare whether two <code>PosInOccurrence</code>s are equal. This can be done using
     * <code>equals</code> or <code>eqEquals</code> (checking for same or equal formulas), which has
     * to be decided by the subclasses
     */
    protected abstract boolean comparePio(TacletApp newApp, TacletApp oldApp,
            PosInOccurrence newPio,
            PosInOccurrence oldPio);

    /**
     * Check whether the old rule application <code>ruleCmp</code> is a duplicate of the new
     * application <code>newApp</code> at position <code>newPio</code>.<code>newPio</code> can be
     * <code>null</code>
     */
    protected boolean sameApplication(RuleApp ruleCmp, TacletApp newApp, PosInOccurrence newPio) {
        // compare the rules
        if (newApp.rule() != ruleCmp.rule()) {
            return false;
        }

        final TacletApp cmp = (TacletApp) ruleCmp;

        // compare the position of application
        if (newPio != null) {
            if (!(cmp instanceof PosTacletApp)) {
                return false;
            }
            final PosInOccurrence oldPio = cmp.posInOccurrence();
            if (!comparePio(newApp, cmp, newPio, oldPio)) {
                return false;
            }
        }


        // compare the if-sequent instantiations
        final ImmutableList<AssumesFormulaInstantiation> newAppIfFmlInstantiations =
            newApp.assumesFormulaInstantiations();
        final ImmutableList<AssumesFormulaInstantiation> cmpIfFmlInstantiations =
            cmp.assumesFormulaInstantiations();
        if (newAppIfFmlInstantiations == null || cmpIfFmlInstantiations == null) {
            if (newAppIfFmlInstantiations != null || cmpIfFmlInstantiations != null) {
                return false;
            }
        } else {

            final Iterator<AssumesFormulaInstantiation> it0 = newAppIfFmlInstantiations.iterator();
            final Iterator<AssumesFormulaInstantiation> it1 = cmpIfFmlInstantiations.iterator();

            while (it0.hasNext()) {
                // this test should be improved
                if (it0.next().getSequentFormula() != it1.next().getSequentFormula()) {
                    return false;
                }
            }
        }

        return equalInterestingInsts(newApp.instantiations(), cmp.instantiations());
    }

    private boolean equalInterestingInsts(SVInstantiations inst0, SVInstantiations inst1) {
        if (!equalUpdateContext(inst0.getUpdateContext(), inst1.getUpdateContext())) {
            return false;
        }

        final var interesting0 = inst0.interesting();
        final var interesting1 = inst1.interesting();
        return subset(interesting0, interesting1) && subset(interesting1, interesting0);
    }

    /**
     * Fast rejection for the label-insensitive comparisons of this class: two terms that are
     * equal up to term labels are in particular equal up to renaming of bound variables
     * (renaming equality ignores labels), so their cached renaming hash is equal, and a
     * differing hash proves inequality without walking the terms. Terms carrying a program are
     * left to the full comparison: their renaming hash would walk the whole program, which is
     * expensive for terms that live only a few rounds.
     */
    private static boolean cannotBeEqualModLabels(JTerm a, JTerm b) {
        return !a.containsJavaBlockRecursive() && !b.containsJavaBlockRecursive()
                && a.hashCodeModRenaming() != b.hashCodeModRenaming();
    }

    /**
     * Compare two update contexts modulo irrelevant term labels. Labels carry history (e.g.
     * origin), and a label-sensitive comparison would let a duplicate escape the veto
     * nondeterministically -- exactly what the surrounding duplicate check avoids. Matches the
     * mod-label focus-term comparison in
     * {@link NonDuplicateAppModPositionFeature#comparePio}, which shares this helper for its
     * update-context part.
     */
    protected static boolean equalUpdateContext(ImmutableList<UpdateLabelPair> ctx0,
            ImmutableList<UpdateLabelPair> ctx1) {
        if (ctx0.size() != ctx1.size()) {
            return false;
        }
        final var it0 = ctx0.iterator();
        final var it1 = ctx1.iterator();
        while (it0.hasNext()) {
            final JTerm u0 = it0.next().update();
            final JTerm u1 = it1.next().update();
            if (cannotBeEqualModLabels(u0, u1)) {
                return false;
            }
            if (!u0.equalsModProperty(u1, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                return false;
            }
        }
        return true;
    }

    private boolean subset(ImmutableMap<SchemaVariable, InstantiationEntry<?>> insts0,
            ImmutableMap<SchemaVariable, InstantiationEntry<?>> insts1) {

        for (ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>> entry0 : insts0) {
            if (entry0.key() instanceof SkolemTermSV || entry0.key() instanceof VariableSV) {
                continue;
            }

            final InstantiationEntry<?> instEntry1 = insts1.get(entry0.key());

            if (instEntry1 == null) {
                return false;
            }
            // instantiation terms are compared modulo term labels: labels carry history (e.g.
            // origin) and would make the duplicate check miss semantically equal applications
            final Object inst0 = entry0.value().getInstantiation();
            final Object inst1 = instEntry1.getInstantiation();
            if (inst0 instanceof JTerm term0 && inst1 instanceof JTerm term1) {
                if (cannotBeEqualModLabels(term0, term1)
                        || !term0.equalsModProperty(term1, IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    return false;
                }
            } else if (!inst0.equals(inst1)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Search for a duplicate of the application <code>app</code> by walking upwards in the proof
     * tree. Here, we assume that <code>pos</code> is non-null, and as an optimisation we stop as
     * soon as we have reached a point where the formula containing the focus no longer occurs in
     * the sequent
     */
    protected boolean noDuplicateFindTaclet(TacletApp app,
            PosInOccurrence pos, Goal goal) {
        final Node node = goal.node();
        final AppliedRuleAppsNameCache cache =
            node.proof().getServices().getCaches().getAppliedRuleAppsNameCache();
        // A duplicate must agree on the focus term up to term labels (every comparePio variant,
        // including the modulo-position one, implies this), so it shares the candidate's focus-term
        // fingerprint and can only be in that bucket -- PROVIDED the fingerprint itself ignores
        // term labels, matching the equality the buckets are probed with: a label-sensitive
        // fingerprint would put a duplicate whose focus differs only in (history-dependent, e.g.
        // origin) labels into a different bucket, where it would silently escape the veto.
        // AppliedRuleAppsNameCache#focusFingerprint is label-insensitive by construction. A
        // find-less application (pos == null) lands in bucket 0, where all find-less applications
        // of
        // this name live (a taclet name is either find or find-less, never both).
        final int fingerprint = pos == null ? 0
                : AppliedRuleAppsNameCache.focusFingerprint(pos.subTerm());
        List<RuleApp> apps = cache.get(node, app.rule().name(), fingerprint);

        // Check all rules with this name in the same fingerprint bucket
        for (RuleApp a : apps) {
            if (sameApplication(a, app, pos)) {
                return false;
            }
        }

        return true;
    }

}
