/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

/**
 * This class captures a proof macro which is meant to fully automise KeY proof workflow.
 *
 * It is experimental.
 *
 * It performs the following steps:
 * <ol>
 * <li>Finish symbolic execution
 * <li>>Separate proof obligations" +
 * <li>Expand invariant definitions
 * <li>Try to close all proof obligations
 * </ol>
 *
 * @author mattias ulbrich
 */
public class FullAutoPilotProofMacro extends SequentialProofMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro} before retracting.
     * This overrides the strategy setting.
     */
    private static final int NUMBER_OF_TRY_STEPS =
        Integer.getInteger("key.autopilot.closesteps", 1000);

    @Override
    public String getName() {
        return "Full Auto Pilot";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getScriptCommandName() {
        return "autopilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution" + "<li>Separate proof obligations"
            + "<li>Expand invariant definitions" + "<li>Try to close all proof obligations</ol>";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new AutoPilotPrepareProofMacro(),
            new TryCloseMacro(NUMBER_OF_TRY_STEPS) };
    }
}
