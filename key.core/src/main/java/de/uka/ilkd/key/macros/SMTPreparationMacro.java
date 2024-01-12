/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

/**
 * A macro that performs all simplifications that are necessary in order to perform a translation of
 * the sequent to SMT. These include symbolic execution and heap simplification.
 *
 * @author js
 */
public class SMTPreparationMacro extends SequentialProofMacro {
    /**
     * Creates the proof macro array.
     * <p>
     * Override this method by returning an array with the macros you want to call in the order of
     * execution.
     *
     * @return a non-null array which should not be altered afterwards.
     */
    @Override
    protected ProofMacro[] createProofMacroArray() {
        ProofMacro[] macros = new ProofMacro[2];
        macros[0] = new AutoPilotPrepareProofMacro();
        macros[1] = new HeapSimplificationMacro();
        return macros;
    }

    /**
     * Gets the name of this macro.
     * <p>
     * Used as menu entry
     *
     * @return a non-<code>null</code> constant string
     */
    @Override
    public String getName() {
        return "SMT Preparation";
    }

    /**
     * Gets the category of this macro.
     * <p>
     * Used as name of the menu under which the macro is sorted. Return <code>null</code> if no
     * submenu is to be created.
     *
     * @return a constant string, or <code>null</code>
     */
    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    /**
     * Gets the description of this macro.
     * <p>
     * Used as tooltip.
     *
     * @return a non-<code>null</code> constant string
     */
    @Override
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution" + "<li>Separate proof obligations"
            + "<li>Expand invariant definitions" + "<li>Simplify heap expressions</ol>";
    }
}
