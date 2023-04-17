// This file is part of the RECODER library and protected by the LGPL.
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
