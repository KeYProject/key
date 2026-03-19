/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.indexing;

import java.util.HashMap;
import java.util.LinkedHashMap;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.sequent.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Class to manage the tags of the formulas of a sequent (node). Instances of this class are stored
 * by instances of the <code>Goal</code> class, and are not immutable
 */
public final class FormulaTagManager {

    // Maps for the assignment of tags to formulas and vice versa

    /** Key: FormulaTag Value: FormulaInfo */
    private final HashMap<FormulaTag, FormulaInfo> tagToFormulaInfo;

    /** Key: PosInOccurrence Value: FormulaTag */
    private final HashMap<PosInOccurrence, FormulaTag> pioToTag;

    /**
     * Create a new manager that is initialised with the formulas of the given sequent
     */
    public FormulaTagManager(ProofGoal<?> p_goal) {
        tagToFormulaInfo = new LinkedHashMap<>();
        pioToTag = new LinkedHashMap<>();
        createNewTags(p_goal);
    }

    private FormulaTagManager(HashMap<FormulaTag, FormulaInfo> p_tagToPIO,
            HashMap<PosInOccurrence, FormulaTag> p_pioToTag) {
        tagToFormulaInfo = p_tagToPIO;
        pioToTag = p_pioToTag;
    }

    /**
     * @return the tag of the formula at the given position
     */
    public @Nullable FormulaTag getTagForPos(PosInOccurrence p_pio) {
        return pioToTag.get(p_pio);
    }

    /**
     * @return The current position of the formula with the given tag; the sequent attribute of the
     *         returned <code>PosInOccurrence</code> can be obsolete and refer to a previous node.
     *         If no formula is assigned to the given tag, <code>null</code> is returned
     */
    public @Nullable PosInOccurrence getPosForTag(FormulaTag p_tag) {
        final FormulaInfo info = getFormulaInfo(p_tag);
        if (info == null) {
            return null;
        }
        return info.pio;
    }

    /**
     * @return The age (as obtained by <code>Goal.getTime()</code>) of the formula, i.e. the time
     *         when the formula was introduced resp. when the last modification was applied to the
     *         formula. If no formula is assigned to the given tag, <code>0</code> is returned
     */
    public long getAgeForTag(FormulaTag p_tag) {
        final FormulaInfo info = getFormulaInfo(p_tag);
        if (info == null) {
            return 0;
        }
        return info.age;
    }

    /**
     * The provided tag must be actively managed by the {@link FormulaTagManager}
     *
     * @return All modifications that were applied to the formula with the given tag since the
     *         creation of the tag, starting with the most recent one
     * @throws NullPointerException if the provided tag is not managed by this manager
     */
    public ImmutableList<@NonNull FormulaChangeInfo> getModifications(FormulaTag p_tag) {
        final FormulaInfo formulaInfo = getFormulaInfo(p_tag);
        assert formulaInfo != null
                : "@AssumeAssertion(nullness): Method should only be called for valid/existing tags";
        return formulaInfo.modifications;
    }

    public void sequentChanged(SequentChangeInfo sci, long newAge) {
        removeTags(sci, true);
        removeTags(sci, false);

        updateTags(sci, true, newAge);
        updateTags(sci, false, newAge);

        addTags(sci, true, newAge);
        addTags(sci, false, newAge);
    }

    private void updateTags(SequentChangeInfo sci, boolean p_antec, long newAge) {
        for (var formulaChangeInfo : sci.modifiedFormulas(p_antec)) {
            updateTag(formulaChangeInfo, newAge);
        }
    }

    private void addTags(SequentChangeInfo sci, boolean p_antec, long age) {
        for (SequentFormula sf : sci.addedFormulas(p_antec)) {
            final PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), p_antec);
            createNewTag(pio, age);
        }
    }

    private void removeTags(SequentChangeInfo sci, boolean p_antec) {
        for (SequentFormula sf : sci.removedFormulas(p_antec)) {
            final PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), p_antec);
            removeTag(pio);
        }
    }

    @Override
    @SuppressWarnings("unchecked")
    public Object clone() {
        return new FormulaTagManager((HashMap<FormulaTag, FormulaInfo>) tagToFormulaInfo.clone(),
            (HashMap<PosInOccurrence, FormulaTag>) pioToTag.clone());
    }

    public FormulaTagManager copy() {
        return (FormulaTagManager) clone();
    }


    /**
     * Create new tags for all formulas of a sequent
     *
     * @param p_goal The sequent
     */
    private void createNewTags(ProofGoal<?> p_goal) {
        final Sequent seq = p_goal.sequent();
        final long age = p_goal.getTime();
        createNewTags(seq.succedent(), age, false);
        createNewTags(seq.antecedent(), age, true);
    }

    /**
     * Create new tags for all formulas of a semisequent
     *
     * @param semisequent the {@link Semisequent} for which to create the tags
     * @param newAge a long indicating the age of the {@link ProofGoal} to which the semisequent
     *        belongs
     * @param p_antec true iff the semisequent is an antecedent
     */
    private void createNewTags(Semisequent semisequent, long newAge, boolean p_antec) {
        for (SequentFormula s : semisequent) {
            final PosInOccurrence pio =
                new PosInOccurrence(s, PosInTerm.getTopLevel(), p_antec);
            createNewTag(pio, newAge);
        }
    }

    /**
     * Add a new tag to the maps
     *
     * @param p_pio The formula for which a new tag is supposed to be created
     */
    private void createNewTag(PosInOccurrence p_pio, long age) {
        final FormulaTag tag = new FormulaTag();
        tagToFormulaInfo.put(tag, new FormulaInfo(p_pio, age));
        pioToTag.put(p_pio, tag);
    }

    /**
     * Remove the entries for the given formulas from the maps
     */
    private void removeTag(PosInOccurrence p_pio) {
        final FormulaTag tag = getTagForPos(p_pio);

        assert tag != null
                : "@AssumeAssertion(nullness): Tried to remove a tag that does not exist";

        tagToFormulaInfo.remove(tag);
        putInQueryCache(tag, null);
        pioToTag.remove(p_pio);
    }

    private void updateTag(FormulaChangeInfo p_info, long newAge) {
        final PosInOccurrence oldPIO = p_info.positionOfModification().topLevel();
        final FormulaTag tag = getTagForPos(oldPIO);
        assert tag != null
                : "@AssumeAssertion(nullness): Tried to update a tag that does not exist";
        final FormulaInfo oldInfo = getFormulaInfo(tag);
        assert oldInfo != null
                : "@AssumeAssertion(nullness): Tried to update a tag with no previous information";
        final FormulaInfo newInfo = oldInfo.addModification(p_info, newAge);

        tagToFormulaInfo.put(tag, newInfo);
        putInQueryCache(tag, newInfo);
        pioToTag.remove(oldPIO);
        pioToTag.put(newInfo.pio, tag);
    }

    ////////////////////////////////////////////////////////////////////////////
    // Simple cache for <code>getFormulaInfo</code>

    private @Nullable FormulaTag lastTagQueried = null;
    private @Nullable FormulaInfo lastQueryResult = null;

    private void putInQueryCache(FormulaTag p_tag, @Nullable FormulaInfo p_info) {
        lastTagQueried = p_tag;
        lastQueryResult = p_info;
    }

    ////////////////////////////////////////////////////////////////////////////

    private @Nullable FormulaInfo getFormulaInfo(FormulaTag p_tag) {
        if (lastTagQueried != p_tag) {
            putInQueryCache(p_tag, tagToFormulaInfo.get(p_tag));
        }
        return lastQueryResult;
    }

    /// retrieves the age for the given position
    /// @param pio the [PosInOccurrence] of the formula whose age is queries
    /// @return the age for the given position
    /// @throws IllegalStateException if pos in occurrence does not describe a known formula
    public long getAgeForPos(PosInOccurrence pio) {
        final FormulaTag tag = getTagForPos(pio);
        if (tag == null) {
            throw new IllegalStateException("Formula tag for " + pio + " not found");
        }
        return getAgeForTag(tag);
    }


    /**
     * Class that holds information about a formula, namely the current position
     * (<code>PosInOccurrence</code>) as well as a list of the modifications that have been applied
     * to the formula so far. Instances of this class are immutable
     */
    private static class FormulaInfo {
        /*
         * (non-Javadoc)
         *
         * @see java.lang.Object#toString()
         */
        @Override
        public String toString() {
            return "FormulaInfo [pio=" + pio + ", modifications=" + modifications + ", age=" + age
                + "]";
        }

        public final PosInOccurrence pio;
        /**
         * All modifications that have been applied to the formula since the creation of the tag.
         * The most recent modification is the first element of the list
         */
        public final ImmutableList<FormulaChangeInfo> modifications;

        /**
         * The age (as obtained by <code>Goal.getTime()</code>) of the formula, i.e. the time when
         * the formula was introduced resp. when the last modification was applied to the formula
         */
        public final long age;

        public FormulaInfo(PosInOccurrence pio, long age) {
            this(pio, ImmutableSLList.nil(), age);
        }

        private FormulaInfo(PosInOccurrence pio, ImmutableList<FormulaChangeInfo> modifications,
                long age) {
            this.pio = pio;
            this.modifications = modifications;
            this.age = age;
        }

        public FormulaInfo addModification(FormulaChangeInfo p_info, long p_age) {
            final PosInOccurrence newPIO =
                new PosInOccurrence(p_info.newFormula(), PosInTerm.getTopLevel(), pio.isInAntec());

            return new FormulaInfo(newPIO, modifications.prepend(p_info), p_age);
        }
    }

}
