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
public class FullUseInformationFlowContractMacro extends SequentialProofMacro {

    @Override
    public String getName() {
        return "Use information flow contracts";
    }

    @Override
    public String getDescription() {
        return "Applies all applicable information flow contract rules and " +
                "prepares the information flow pre branches.";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] {
                new UseInformationFlowContractMacro(),
                new PrepareInfFlowContractPreBranchesMacro()
        };
    }

}
