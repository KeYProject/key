/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Class to manage the tags of the formulas of a sequent (node). Instances of this class are stored
 * by instances of the <code>Goal</code> class, and are not immutable
 */
public class FormulaTagManager {

    /** Maps for the assignment of tags to formulas and vice versa */

    /** Key: FormulaTag Value: FormulaInfo */
    private final HashMap<FormulaTag, FormulaInfo> tagToFormulaInfo;

    /** Key: PosInOccurrence Value: FormulaTag */
    private final HashMap<PosInOccurrence, FormulaTag> pioToTag;

    /**
     * Create a new manager that is initialised with the formulas of the given sequent
     */
    FormulaTagManager(Goal p_goal) {
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
    public FormulaTag getTagForPos(PosInOccurrence p_pio) {
        return pioToTag.get(p_pio);
    }

    /**
     * @return The current position of the formula with the given tag; the sequent attribute of the
     *         returned <code>PosInOccurrence</code> can be obsolete and refer to a previous node.
     *         If no formula is assigned to the given tag, <code>null</code> is returned
     */
    public PosInOccurrence getPosForTag(FormulaTag p_tag) {
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
     * @return All modifications that were applied to the formula with the given tag since the
     *         creation of the tag, starting with the most recent one
     */
    public ImmutableList<FormulaChangeInfo> getModifications(
            FormulaTag p_tag) {
        return getFormulaInfo(p_tag).modifications;
    }


    public void sequentChanged(Goal source,
            SequentChangeInfo sci) {
        assert source != null;
        removeTags(sci, true, source);
        removeTags(sci, false, source);

        updateTags(sci, true, source);
        updateTags(sci, false, source);

        addTags(sci, true, source);
        addTags(sci, false, source);
    }

    private void updateTags(SequentChangeInfo sci,
            boolean p_antec, Goal p_goal) {
        for (var formulaChangeInfo : sci.modifiedFormulas(p_antec)) {
            updateTag(formulaChangeInfo, p_goal);
        }
    }

    private void addTags(SequentChangeInfo sci,
            boolean p_antec, Goal p_goal) {
        for (SequentFormula sf : sci.addedFormulas(p_antec)) {
            final PosInOccurrence pio = new PosInOccurrence(sf, PosInTerm.getTopLevel(), p_antec);
            createNewTag(pio, p_goal);
        }
    }

    private void removeTags(SequentChangeInfo sci,
            boolean p_antec, Goal p_goal) {
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
    private void createNewTags(Goal p_goal) {
        createNewTags(p_goal, false);
        createNewTags(p_goal, true);
    }

    /**
     * Create new tags for all formulas of a semisequent
     *
     * @param p_goal The sequent that contains the semisequent
     * @param p_antec true iff the formulas of the antecedent should be added
     */
    private void createNewTags(Goal p_goal, boolean p_antec) {
        final Sequent seq = p_goal.sequent();
        final Semisequent ss = p_antec ? seq.antecedent() : seq.succedent();

        for (SequentFormula s : ss) {
            final PosInOccurrence pio =
                new PosInOccurrence(s, PosInTerm.getTopLevel(), p_antec);
            createNewTag(pio, p_goal);
        }
    }

    /**
     * Add a new tag to the maps
     *
     * @param p_pio The formula for which a new tag is supposed to be created
     */
    private void createNewTag(PosInOccurrence p_pio, Goal p_goal) {
        final FormulaTag tag = new FormulaTag();
        tagToFormulaInfo.put(tag, new FormulaInfo(p_pio, p_goal.getTime()));
        pioToTag.put(p_pio, tag);
    }

    /**
     * Remove the entries for the given formulas from the maps
     */
    private void removeTag(PosInOccurrence p_pio) {
        final FormulaTag tag = getTagForPos(p_pio);

        Debug.assertFalse(tag == null, "Tried to remove a tag that does not exist");

        tagToFormulaInfo.remove(tag);
        putInQueryCache(tag, null);
        pioToTag.remove(p_pio);
    }

    private void updateTag(FormulaChangeInfo p_info, Goal p_goal) {
        final PosInOccurrence oldPIO =
            p_info.positionOfModification().topLevel();
        final FormulaTag tag = getTagForPos(oldPIO);
        final FormulaInfo oldInfo = getFormulaInfo(tag);
        final FormulaInfo newInfo = oldInfo.addModification(p_info, p_goal.getTime());

        tagToFormulaInfo.put(tag, newInfo);
        putInQueryCache(tag, newInfo);
        pioToTag.remove(oldPIO);
        pioToTag.put(newInfo.pio, tag);
    }

    ////////////////////////////////////////////////////////////////////////////
    // Simple cache for <code>getFormulaInfo</code>

    private FormulaTag lastTagQueried = null;
    private FormulaInfo lastQueryResult = null;

    private void putInQueryCache(FormulaTag p_tag, FormulaInfo p_info) {
        lastTagQueried = p_tag;
        lastQueryResult = p_info;
    }

    ////////////////////////////////////////////////////////////////////////////

    private FormulaInfo getFormulaInfo(FormulaTag p_tag) {
        if (lastTagQueried != p_tag) {
            putInQueryCache(p_tag, tagToFormulaInfo.get(p_tag));
        }
        return lastQueryResult;
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

        public FormulaInfo(PosInOccurrence p_pio, long p_age) {
            this(p_pio, ImmutableSLList.nil(), p_age);
        }

        private FormulaInfo(PosInOccurrence p_pio,
                ImmutableList<FormulaChangeInfo> p_modifications,
                long p_age) {
            pio = p_pio;
            modifications = p_modifications;
            age = p_age;
        }

        public FormulaInfo addModification(
                FormulaChangeInfo p_info,
                long p_age) {
            final PosInOccurrence newPIO =
                new PosInOccurrence(p_info.newFormula(), PosInTerm.getTopLevel(), pio.isInAntec());

            return new FormulaInfo(newPIO,
                modifications.prepend(p_info),
                p_age);
        }
    }

}
