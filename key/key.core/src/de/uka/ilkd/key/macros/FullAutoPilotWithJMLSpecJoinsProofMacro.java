// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.macros;

/**
 * This class captures a proof macro which is meant to fully automate the KeY proof
 * workflow.<p>
 *
 * It is experimental.
 *
 * It performs the following steps:
 * <ol>
 * <li>Finish symbolic execution with join specifications
 * <li>Try to close all proof obligations
 * </ol>
 *
 * @author Mattias Ulbrich
 * @author Dominic Scheurer
 * 
 * @see FullAutoPilotProofMacro
 */
public class FullAutoPilotWithJMLSpecJoinsProofMacro extends SequentialProofMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro}
     * before retracting. This overrides the strategy setting.
     */
    private static final int NUMBER_OF_TRY_STEPS =
            Integer.getInteger("key.autopilot.closesteps", 1000);

    @Override
    public String getName() {
        return "Full Auto Pilot with joins specified in JML";
    }

    @Override
    public String getCategory() {
        return "Join";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution (with joins specified by JML annotations)" +
                "<li>Try to close all proof obligations</ol>";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {
                new FinishSymbolicExecutionWithSpecJoinsMacro(),
                new TryCloseMacro(NUMBER_OF_TRY_STEPS)
        };
    }
}
