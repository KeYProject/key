/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import recoder.ProgramFactory;

public class ProofCrossReferenceServiceConfiguration extends KeYCrossReferenceServiceConfiguration {

    public ProofCrossReferenceServiceConfiguration(KeYRecoderExcHandler keh) {
        super(keh);
    }

    /** we need another factory for some new program elements */
    protected ProgramFactory makeProgramFactory() {
        return ProofJavaProgramFactory.getInstance();
    }

}
