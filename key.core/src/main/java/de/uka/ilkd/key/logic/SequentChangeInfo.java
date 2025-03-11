/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Records the changes made to a sequent. Keeps track of added and removed formula to one of the
 * semisequents. The intersection of added and removed formulas of the same semisequent may not be
 * empty, in particular this means that a formula added and removed afterwards will occur in both
 * lists. The situation where this can happen is that a list of formulas had to be added to the
 * sequent and the list has not been redundancy free.
 */
public class SequentChangeInfo {

    /**
     * change information related to the antecedent, this means the there added and removed formulas
     */
    private SemisequentChangeInfo antecedent;

    /**
     * change information related to the antecedent, this means the there added and removed formulas
     */
    private SemisequentChangeInfo succedent;

    /**
     * the sequent before the changes
     */
    private final Sequent originalSequent;

    /**
     * the sequent after the changes
     */
    private Sequent resultingSequent;

    /**
     * creates a new sequent change info whose semisequent described by position pos has changed.
     * The made changes are stored in semiCI and the resulting sequent is given by result
     *
     * @param pos the PosInOccurrence describing the semisequent where the changes took place
     * @param semiCI the SemisequentChangeInfo describing the changes in detail (which formulas have
     *        been added/removed)
     * @return the sequent change information object describing the complete changes made to the
     *         sequent together with the operations result.
     */
    public static SequentChangeInfo createSequentChangeInfo(PosInOccurrence pos,
            SemisequentChangeInfo semiCI, Sequent result, Sequent original) {
        return createSequentChangeInfo(pos.isInAntec(), semiCI, result, original);
    }

    /**
     * creates a new sequent change info whose semisequent described by the value of the selector
     * antec (true selects antecedent; false selects succedent) has changed. The made changes are
     * stored in semiCI and the resulting sequent is given by result
     *
     * @param antec a boolean indicating if the given semisequent change information describes the
     *        changes of the antecedent or succedent
     * @param semiCI the SemisequentChangeInfo describing the changes in detail (which formulas have
     *        been added/removed)
     * @param result the Sequent which is the result of the changes
     * @param original the Sequent to which the described changes have been applied
     * @return the sequent change information object describing the complete changes made to the
     *         sequent together with the operations result.
     */
    public static SequentChangeInfo createSequentChangeInfo(boolean antec,
            SemisequentChangeInfo semiCI, Sequent result, Sequent original) {
        if (antec) {
            return new SequentChangeInfo(semiCI, null, result, original);
        } else {
            return new SequentChangeInfo(null, semiCI, result, original);
        }
    }

    /**
     * creates a new sequent change info whose semisequents have changed. The made changes are
     * stored in semiCI and the resulting sequent is given by result
     *
     * @param anteCI the SemisequentChangeInfo describing the changes of the antecedent in detail
     *        (which formulas have been added/removed)
     * @param sucCI the SemisequentChangeInfo describing the changes of the succedent detail (which
     *        formulas have been added/removed)
     * @return the sequent change information object describing the complete changes made to the
     *         sequent together with the operations result.
     */
    public static SequentChangeInfo createSequentChangeInfo(SemisequentChangeInfo anteCI,
            SemisequentChangeInfo sucCI, Sequent result, Sequent original) {
        return new SequentChangeInfo(anteCI, sucCI, result, original);
    }

    /**
     * creates a new sequent change information object. Therefore, it combines the changes to the
     * semisequents of the sequent.
     *
     * @param antecedent the SemisequentChangeInfo describing the changes of the antecedent
     * @param succedent the SemisequentChangeInfo describing the changes of the succedent
     * @param resultingSequent the Sequent being the result of the changes
     * @param originalSequent the Sequent that has been transformed
     */
    private SequentChangeInfo(SemisequentChangeInfo antecedent, SemisequentChangeInfo succedent,
            Sequent resultingSequent, Sequent originalSequent) {
        this.antecedent = antecedent;
        this.succedent = succedent;
        this.resultingSequent = resultingSequent;
        this.originalSequent = originalSequent;
    }

    public SequentChangeInfo copy() {
        return new SequentChangeInfo(
            antecedent == null ? null : antecedent.copy(),
            succedent == null ? null : succedent.copy(),
            resultingSequent,
            originalSequent);
    }

    /**
     * returns true iff the sequent has been changed by the operation
     *
     * @return true iff the sequent has been changed by the operation
     */
    public boolean hasChanged() {
        return (antecedent != null && antecedent.hasChanged())
                || (succedent != null && succedent.hasChanged());
    }

    /**
     * returns true if the selected part of sequent has changed. Thereby the flag 'antec' specifies
     * the selection: true selects the antecedent and false the succedent of the sequent.
     *
     * @return true iff the sequent has been changed by the operation
     */
    public boolean hasChanged(boolean antec) {
        return antec ? (antecedent != null && antecedent.hasChanged())
                : (succedent != null && succedent.hasChanged());
    }

    public SemisequentChangeInfo getSemisequentChangeInfo(boolean antec) {
        return antec ? antecedent : succedent;
    }

    /**
     * The formulas added to one of the semisequents are returned. The selected semisequent depends
     * on the value of selector 'antec' which is the antecedent if 'antec' is true and the succedent
     * otherwise.
     *
     * @param antec a boolean used to select one of the two semisequents of a sequent (true means
     *        antecedent; false means succedent)
     * @return list of formulas added to the selected semisequent
     */
    public ImmutableList<SequentFormula> addedFormulas(boolean antec) {
        return antec
                ? (antecedent != null ? antecedent.addedFormulas() : ImmutableSLList.nil())
                : (succedent != null ? succedent.addedFormulas() : ImmutableSLList.nil());
    }

    /**
     * The formulas added to the sequent are returned as a concatenated list of the formulas added
     * to each semisequent.
     *
     * @return list of formulas added to sequent
     */
    public ImmutableList<SequentFormula> addedFormulas() {
        final ImmutableList<SequentFormula> addedFormulasAntec = addedFormulas(true);
        final ImmutableList<SequentFormula> addedFormulasSucc = addedFormulas(false);

        return concatenateHelper(addedFormulasAntec, addedFormulasSucc);

    }

    /**
     * The formulas removed from one of the semisequents are returned. The selected semisequent
     * depends on the value of selector 'antec' which is the antecedent if 'antec' is true and the
     * succedent otherwise.
     *
     * @param antec a boolean used to select one of the two semisequents of a sequent (true means
     *        antecedent; false means succedent)
     * @return list of formulas removed from the selected semisequent
     */
    public ImmutableList<SequentFormula> removedFormulas(boolean antec) {
        return antec
                ? (antecedent != null ? antecedent.removedFormulas() : ImmutableSLList.nil())
                : (succedent != null ? succedent.removedFormulas() : ImmutableSLList.nil());
    }

    /**
     * The formulas removed from the sequent are returned as a concatenated list of the formulas
     * removed from each semisequent.
     *
     * @return list of formulas removed from the sequent
     */
    public ImmutableList<SequentFormula> removedFormulas() {
        final ImmutableList<SequentFormula> removedFormulasAntec = removedFormulas(true);
        final ImmutableList<SequentFormula> removedFormulasSucc = removedFormulas(false);

        return concatenateHelper(removedFormulasAntec, removedFormulasSucc);
    }

    /**
     * The formulas modified within one of the semisequents are returned. The selected semisequent
     * depends on the value of selector 'antec' which is the antecedent if 'antec' is true and the
     * succedent otherwise.
     *
     * @param antec a boolean used to select one of the two semisequents of a sequent (true means
     *        antecedent; false means succedent)
     * @return list of formulas modified within the selected semisequent
     */
    public ImmutableList<FormulaChangeInfo> modifiedFormulas(boolean antec) {
        return antec
                ? (antecedent != null ? antecedent.modifiedFormulas() : ImmutableSLList.nil())
                : (succedent != null ? succedent.modifiedFormulas() : ImmutableSLList.nil());
    }

    /**
     * The formulas modified within the sequent are returned as a concatenated list of the formulas
     * modified within each semisequent.
     *
     * @return list of formulas modified to sequent
     */
    public ImmutableList<FormulaChangeInfo> modifiedFormulas() {
        final ImmutableList<FormulaChangeInfo> modifiedFormulasAntec = modifiedFormulas(true);
        final ImmutableList<FormulaChangeInfo> modifiedFormulasSucc = modifiedFormulas(false);

        return concatenateHelper(modifiedFormulasAntec, modifiedFormulasSucc);
    }

    /**
     * Returns the formulas that have been rejected when trying to add as being redundant.
     *
     * @param antec a boolean used to select one of the two semisequents of a sequent (true means
     *        antecedent; false means succedent)
     * @return list of formulas rejected when trying to add to the selected semisequent
     */
    public ImmutableList<SequentFormula> rejectedFormulas(boolean antec) {
        return antec
                ? (antecedent != null ? antecedent.rejectedFormulas() : ImmutableSLList.nil())
                : (succedent != null ? succedent.rejectedFormulas() : ImmutableSLList.nil());
    }

    /**
     * Returns the formulas that have been rejected when trying to add as being redundant.
     *
     * @return list of rejected formulas
     */
    public ImmutableList<SequentFormula> rejectedFormulas() {
        final ImmutableList<SequentFormula> rejectedFormulasAntec = rejectedFormulas(true);
        final ImmutableList<SequentFormula> rejectedFormulasSucc = rejectedFormulas(false);

        return concatenateHelper(rejectedFormulasAntec, rejectedFormulasSucc);
    }

    /**
     * concatenates the two lists in arbitrary but deterministic order
     *
     * @param antecList the list of antecedent elements
     * @param succList the list of succeden elements
     * @return the concatenated list
     */
    private <T> ImmutableList<T> concatenateHelper(final ImmutableList<T> antecList,
            final ImmutableList<T> succList) {
        final int sizeAntec = antecList.size();
        final int sizeSucc = succList.size();

        if (sizeAntec == 0) {
            return succList;
        } else if (sizeSucc == 0) {
            return antecList;
        } else {
            return sizeAntec > sizeSucc ? succList.prepend(antecList) : antecList.prepend(succList);
        }
    }

    /**
     * This method combines the change information from this info and its successor. ATTENTION: it
     * takes over ownership over {@code succ} and does not release it. This means when invoking the
     * method it must be ensured that {@code succ} is never used afterwards.
     */
    public void combine(SequentChangeInfo succ) {
        final SequentChangeInfo antec = this;
        if (antec == succ) {
            return;
        }

        antec.resultingSequent = succ.resultingSequent;

        if (antec.antecedent != succ.antecedent) {
            if (antec.antecedent == null) {
                antec.antecedent = succ.antecedent;
            } else if (succ.antecedent != null) {
                antec.antecedent.combine(succ.antecedent);
            }
        }

        if (antec.succedent != succ.succedent) {
            if (antec.succedent == null) {
                antec.succedent = succ.succedent;
            } else if (succ.succedent != null) {
                antec.succedent.combine(succ.succedent);
            }
        }
    }


    /**
     * @return the original sequent
     */
    public Sequent getOriginalSequent() {
        return originalSequent;
    }

    /**
     * returns the resulting sequent
     *
     * @return the resulting sequent
     */
    public Sequent sequent() {
        return resultingSequent;
    }

    /**
     * toString helper
     */
    private String toStringHelp(boolean antec) {
        String result = "";
        if (hasChanged(antec)) {
            result += "\t added:" + addedFormulas(antec);
            result += "\t removed:" + removedFormulas(antec);
            result += "\t modified:" + modifiedFormulas(antec);
        }
        return result;
    }

    /**
     * toString
     */
    public String toString() {
        String result = "antecedent: " + hasChanged(true);
        result += toStringHelp(true);

        result += "\n succedent: " + hasChanged(false);
        result += toStringHelp(false);

        return result;
    }
}
