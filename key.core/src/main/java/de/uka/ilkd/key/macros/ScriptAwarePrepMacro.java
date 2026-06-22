/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.macros;

/**
 * A proof macro that automates the KeY proof workflow when JML proof scripts are present,
 * without attempting to close goals.
 * <p>
 * This macro executes a sequence of sub-macros to handle proofs with embedded JML scripts:
 * </p>
 * <ol>
 * <li>Completes symbolic execution phase</li>
 * <li>Applies JML proof scripts via {@link ApplyScriptsMacro}</li>
 * <li>Does not attempt to close provable goals (unlike {@link ScriptAwareMacro})</li>
 * </ol>
 * <p>
 * The macro is accessible via the script command {@code "script-prep-auto"} and is categorized
 * under "Auto Pilot". It is useful for preparing proofs for further manual interaction.
 * </p>
 *
 * @author mattias ulbrich
 * @see ScriptAwareMacro
 * @see ApplyScriptsMacro
 */
public class ScriptAwarePrepMacro extends SequentialProofMacro {

    private final ProofMacro autoMacro = new SymbolicExecutionOnlyMacro();
    private final ApplyScriptsMacro applyMacro = new ApplyScriptsMacro(null);

    @Override
    public String getScriptCommandName() {
        return "script-prep-auto";
    }

    @Override
    public String getName() {
        return "Script-aware Prep Auto";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "Automatically executes JML proof scripts without closing goals";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { autoMacro, applyMacro };
    }
}
