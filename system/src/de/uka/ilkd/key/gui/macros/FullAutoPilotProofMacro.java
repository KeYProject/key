// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.gui.macros;

/**
 * This class captures a proof macro which is meant to fully automise KeY proof
 * workflow.
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
     * The number of proof steps that should be run by the {@link TryCloseMacro}
     * before retracting. This overrides the strategy setting.
     */
    private static final int NUMBER_OF_TRY_STEPS =
            Integer.getInteger("key.autopilot.closesteps", 1000);

    @Override
    public String getName() {
        return "Full Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution" +
                "<li>Separate proof obligations" +
                "<li>Expand invariant definitions" +
                "<li>Try to close all proof obligations</ol>";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {
                new AutoPilotPrepareProofMacro(),
                new TryCloseMacro(NUMBER_OF_TRY_STEPS)
        };
    }

}
