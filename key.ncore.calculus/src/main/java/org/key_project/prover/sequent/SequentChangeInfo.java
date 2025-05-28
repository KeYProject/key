/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/// Records the changes made to a sequent. Keeps track of added and removed formula to one of the
/// semisequents. The intersection of added and removed formulas of the same semisequent may not be
/// empty, in particular this means that a formula added and removed afterward will occur in both
/// lists. The situation where this can happen is that a list of formulas had to be added to the
/// sequent and the list has not been redundancy free.
public class SequentChangeInfo {
    /// change information related to the antecedent, this means the there added and removed
    /// formulas
    private @NonNull SemisequentChangeInfo antecedent;

    /// change information related to the antecedent, this means the there added and removed
    /// formulas
    private @NonNull SemisequentChangeInfo succedent;

    /// the sequent before the changes
    private final Sequent originalSequent;

    /// the sequent after the changes
    private Sequent resultingSequent;

    /// creates a new sequent change info whose semisequent described by the value of the selector
    /// inAntecedent (true selects antecedent; false selects succedent) has changed. The made
    /// changes
    /// are
    /// stored in semiCI and the resulting sequent is given by result
    ///
    /// @param inAntecedent a boolean indicating if the given semisequent change information
    /// describes the
    /// changes of the antecedent or succedent
    /// @param semiCI the SemisequentChangeInfo describing the changes in detail (which formulas
    /// have
    /// been added/removed)
    /// @param result the Sequent which is the result of the changes
    /// @param original the Sequent to which the described changes have been applied
    /// @return the sequent change information object describing the complete changes made to the
    /// sequent together with the operations result.
    public static SequentChangeInfo createSequentChangeInfo(
            boolean inAntecedent, SemisequentChangeInfo semiCI, Sequent result, Sequent original) {
        if (inAntecedent) {
            return new SequentChangeInfo(semiCI,
                new SemisequentChangeInfo(original.succedent().asList()), result, original);
        } else {
            return new SequentChangeInfo(new SemisequentChangeInfo(original.antecedent().asList()),
                semiCI, result, original);
        }
    }

    /// creates a new sequent change info whose semisequents have changed. The made changes are
    /// stored in semiCI and the resulting sequent is given by result
    ///
    /// @param anteCI the SemisequentChangeInfo describing the changes of the antecedent in detail
    /// (which formulas have been added/removed)
    /// @param sucCI the SemisequentChangeInfo describing the changes of the succedent detail (which
    /// formulas have been added/removed)
    /// @return the sequent change information object describing the complete changes made to the
    /// sequent together with the operations result.
    public static SequentChangeInfo createSequentChangeInfo(
            SemisequentChangeInfo anteCI, SemisequentChangeInfo sucCI, Sequent result,
            Sequent original) {
        return new SequentChangeInfo(anteCI, sucCI, result, original);
    }

    public static SequentChangeInfo createSequentChangeInfo(Sequent original) {
        return new SequentChangeInfo(new SemisequentChangeInfo(original.antecedent().asList()),
            new SemisequentChangeInfo(original.succedent().asList()), original, original);
    }


    /// creates a new sequent change information object. Therefore, it combines the changes to the
    /// semisequents of the sequent.
    ///
    /// @param antecedent the [SemisequentChangeInfo] describing the changes of the antecedent
    /// @param succedent the [SemisequentChangeInfo] describing the changes of the succedent
    /// @param resultingSequent the Sequent being the result of the changes
    /// @param originalSequent the Sequent that has been transformed
    private SequentChangeInfo(@NonNull SemisequentChangeInfo antecedent,
            @NonNull SemisequentChangeInfo succedent,
            Sequent resultingSequent, Sequent originalSequent) {
        this.antecedent = antecedent;
        this.succedent = succedent;
        this.resultingSequent = resultingSequent;
        this.originalSequent = originalSequent;
    }

    public SequentChangeInfo copy() {
        return new SequentChangeInfo(antecedent.copy(), succedent.copy(),
            resultingSequent, originalSequent);
    }

    /// returns true iff the sequent has been changed by the operation
    ///
    /// @return true iff the sequent has been changed by the operation
    public boolean hasChanged() {
        return antecedent.hasChanged() || succedent.hasChanged();
    }

    /// returns true if the selected part of sequent has changed. Thereby the flag 'inAntecedent'
    /// specifies
    /// the selection: true selects the antecedent and false the succedent of the sequent.
    ///
    /// @return true iff the sequent has been changed by the operation
    public boolean hasChanged(boolean inAntecedent) {
        return inAntecedent ? antecedent.hasChanged() : succedent.hasChanged();
    }

    public SemisequentChangeInfo getSemisequentChangeInfo(boolean inAntecedent) {
        return inAntecedent ? antecedent : succedent;
    }

    /// The formulas added to one of the semisequents are returned. The selected semisequent depends
    /// on the value of selector 'inAntecedent' which is the antecedent if 'inAntecedent' is true
    /// and
    /// the succedent otherwise.
    ///
    /// @param inAntecedent a boolean used to select one of the two semisequents of a sequent (true
    /// means
    /// antecedent; false means succedent)
    /// @return list of formulas added to the selected semisequent
    public ImmutableList<SequentFormula> addedFormulas(boolean inAntecedent) {
        return inAntecedent ? antecedent.addedFormulas() : succedent.addedFormulas();
    }

    /// The formulas removed from one of the semisequents are returned. The selected semisequent
    /// depends on the value of selector 'inAntecedent' which is the antecedent if 'inAntecedent' is
    /// true and the
    /// succedent otherwise.
    ///
    /// @param inAntecedent a boolean used to select one of the two semisequents of a sequent
    /// (true means antecedent; false means succedent)
    /// @return list of formulas removed from the selected semisequent
    public ImmutableList<SequentFormula> removedFormulas(boolean inAntecedent) {
        return inAntecedent ? antecedent.removedFormulas() : succedent.removedFormulas();
    }

    /// The formulas modified within one of the semisequents are returned. The selected semisequent
    /// depends on the value of selector 'inAntecedent' which is the antecedent if 'inAntecedent'
    /// is true and the succedent otherwise.
    ///
    /// @param inAntecedent a boolean used to select one of the two semisequents of a sequent
    /// (true means antecedent; false means succedent)
    /// @return list of formulas modified within the selected semisequent
    public ImmutableList<FormulaChangeInfo> modifiedFormulas(boolean inAntecedent) {
        return inAntecedent ? antecedent.modifiedFormulas() : succedent.modifiedFormulas();
    }

    /// The formulas modified within the sequent are returned as a concatenated list of the formulas
    /// modified within each semisequent.
    ///
    /// @return list of formulas modified to sequent
    public ImmutableList<FormulaChangeInfo> modifiedFormulas() {
        return concatenateHelper(modifiedFormulas(true), modifiedFormulas(false));
    }

    /// Returns the formulas that have been rejected when trying to add as being redundant.
    ///
    /// @param inAntecedent a boolean used to select one of the two semisequents of a
    /// sequent (true means antecedent; false means succedent)
    /// @return list of formulas rejected when trying to add to the selected semisequent
    public ImmutableList<SequentFormula> rejectedFormulas(boolean inAntecedent) {
        return inAntecedent ? antecedent.rejectedFormulas() : succedent.rejectedFormulas();
    }

    /// Concatenates the two lists in arbitrary but deterministic order
    ///
    /// @param antecedentFormulas the list of formulas constituting the antecedent
    /// @param succedentFormulas the list of formulas constituting the succedent
    /// @return the concatenated list
    private <T> ImmutableList<T> concatenateHelper(final ImmutableList<T> antecedentFormulas,
            final ImmutableList<T> succedentFormulas) {
        final int sizeOfAntecedent = antecedentFormulas.size();
        final int sizeOfSuccedent = succedentFormulas.size();

        if (sizeOfAntecedent == 0) {
            return succedentFormulas;
        } else if (sizeOfSuccedent == 0) {
            return antecedentFormulas;
        } else {
            return sizeOfAntecedent > sizeOfSuccedent
                    ? succedentFormulas.prepend(antecedentFormulas)
                    : antecedentFormulas.prepend(succedentFormulas);
        }
    }

    /// This method combines the change information from this info and its successor. ATTENTION: it
    /// takes over ownership over `succedent` and does not release it. This means when invoking
    /// the method it must be ensured that `succedent` is never used afterwards.
    public void combine(SequentChangeInfo succedent) {
        final SequentChangeInfo antecedent = this;
        if (antecedent == succedent) {
            return;
        }

        antecedent.resultingSequent = succedent.resultingSequent;

        if (antecedent.antecedent != succedent.antecedent) {
            if (!antecedent.antecedent.hasChanged()) {
                antecedent.antecedent = succedent.antecedent;
            } else if (succedent.antecedent.hasChanged()) {
                antecedent.antecedent.combine(succedent.antecedent);
            }
        }

        if (antecedent.succedent != succedent.succedent) {
            if (!antecedent.succedent.hasChanged()) {
                antecedent.succedent = succedent.succedent;
            } else if (succedent.succedent.hasChanged()) {
                antecedent.succedent.combine(succedent.succedent);
            }
        }
    }

    /// @return the original sequent
    public Sequent getOriginalSequent() {
        return originalSequent;
    }

    /// returns the resulting sequent
    ///
    /// @return the resulting sequent
    public Sequent sequent() {
        return resultingSequent;
    }

    /// toString helper
    private String toStringHelp(boolean inAntecedent) {
        String result = "";
        if (hasChanged(inAntecedent)) {
            result += "\t added:" + addedFormulas(inAntecedent);
            result += "\t removed:" + removedFormulas(inAntecedent);
            result += "\t modified:" + modifiedFormulas(inAntecedent);
        }
        return result;
    }

    /// toString
    public String toString() {
        String result = "antecedent: " + hasChanged(true);
        result += toStringHelp(true);

        result += "\n succedent: " + hasChanged(false);
        result += toStringHelp(false);

        return result;
    }
}
