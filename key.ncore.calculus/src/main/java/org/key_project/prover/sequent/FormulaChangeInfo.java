/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.sequent;

/**
 * This record contains information about a modification of a formula in a sequent. The provided
 * position
 * information describes the position of the sub-formula/term in the original formula that has been
 * replaced.
 * The {@link SequentFormula} {@code newFormula} is the modified sequent formula.
 *
 * @param positionOfModification the {@link PosInOccurrence} describing the modification
 *        position in the original sequent formula
 * @param newFormula the {@link SequentFormula} that is the result of the modification
 */
public record FormulaChangeInfo(PosInOccurrence positionOfModification,SequentFormula newFormula){

/**
 * Returns the original (unmodified) sequent formula.
 *
 * @return the original formula
 */
public SequentFormula getOriginalFormula(){return positionOfModification().sequentFormula();}

/**
 * A string describing the modification.
 *
 * @return {@link String} describing the modification
 */
@Override public String toString(){return"Replaced "+positionOfModification+" with "+newFormula;}}
