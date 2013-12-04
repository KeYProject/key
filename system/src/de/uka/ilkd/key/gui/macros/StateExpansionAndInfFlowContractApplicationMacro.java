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
public class StateExpansionAndInfFlowContractApplicationMacro extends SequentialProofMacro {

    @Override
    public String getName() {
        return "Self-composition state expansion with inf flow contracs";
    }

    @Override
    public String getDescription() {
        return "Extract the self-composed states after the merge of the "
                + "symbolic execution goals which is included in the proof "
                + "obligation generation from information flow contracts " +
                "and apply all relevant information flow contracts.";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {
                new SelfcompositionStateExpansionMacro(),
                new PropositionalExpansionWithSimplificationMacro(),
                new FullUseInformationFlowContractMacro()
        };
    }

}
