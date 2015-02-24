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
package de.uka.ilkd.key.macros;


/**
 *
 * @author christoph scheben
 */
public class AuxiliaryComputationAutoPilotMacro extends ExhaustiveProofMacro {

    @Override
    public String getName() {
        return "Auxiliary Computation Auto Pilot";
    }


    @Override
    public String getDescription() {
        return "<html><ol><li>Start auxiliary computation" +
               "<li>Finish symbolic execution" +
               "<li>Try to close as many goals as possible</ol>";
    }


    @Override
    ProofMacro getProofMacro() {
        return new SequentialOnLastGoalProofMacro() {
            /**
             * The number of proof steps that should be run by the
             * {@link TryCloseMacro} before retracting. This overrides the
             * strategy setting.
             */
            private final int NUMBER_OF_TRY_STEPS =
                    Integer.getInteger("key.autopilot.closesteps", 1000);

            @Override
            public String getName() { return ""; }
            @Override
            public String getDescription() { return "Anonymous Macro"; }

            @Override
            protected ProofMacro[] createProofMacroArray() {
                // The FinishSymbolicExecutionMacro and the TryCloseMacro shall be
                // started at the same node. Therefore they are encapsulated in an
                // own (anonymous) SequentialProofMacro.
                SequentialProofMacro finishSymbExecAndTryToClose =
                        new SequentialProofMacro() {
                    @Override
                    protected ProofMacro[] createProofMacroArray() {
                        return new ProofMacro[]{ new FinishSymbolicExecutionMacro(),
                                                 new TryCloseMacro(NUMBER_OF_TRY_STEPS)};
                    }
                    @Override
                    public String getName() { return ""; }
                    @Override
                    public String getDescription() { return "Anonymous Macro"; }
                };

                return new ProofMacro[]{ new StartAuxiliaryComputationMacro(),
                                         finishSymbExecAndTryToClose };
            }
        };
    }
}