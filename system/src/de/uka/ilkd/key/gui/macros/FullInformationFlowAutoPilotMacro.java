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
 *
 * @author christoph scheben
 */
public class FullInformationFlowAutoPilotMacro extends SequentialOnLastGoalProofMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro}
     * before retracting. This overrides the strategy setting if set to a value
     * greater or equal to 0.
     */
    private static final int NUMBER_OF_TRY_STEPS = -1;
//            Integer.getInteger("key.autopilot.closesteps", 1000);

    @Override
    public String getName() {
        return "Full Information Flow Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "...";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        // The StateExpansionAndInfFlowContractApplicationMacro and the
        // TryCloseMacro shell be started at the same node. Therefore they are
        // encapsulated in an own (anonymous) SequentialProofMacro.
        SequentialProofMacro fullmainCompMacro =
                new SequentialProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[]{
                    new StateExpansionAndInfFlowContractApplicationMacro(),
                    new TryCloseMacro(NUMBER_OF_TRY_STEPS)
                };
            }


            @Override
            public String getName() {
                return "Anonymous Macro";
            }


            @Override
            public String getDescription() {
                return "Anonymous Macro";
            }
        };
        return new ProofMacro[]{
            new AuxiliaryComputationAutoPilotMacro(),
            new FinishAuxiliaryComputationMacro(),
            fullmainCompMacro
        };
    }
}
