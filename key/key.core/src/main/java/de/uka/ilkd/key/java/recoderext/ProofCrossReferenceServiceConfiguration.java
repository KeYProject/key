/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.
package de.uka.ilkd.key.java.recoderext;

import recoder.ProgramFactory;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

public class ProofCrossReferenceServiceConfiguration extends KeYCrossReferenceServiceConfiguration {

    public ProofCrossReferenceServiceConfiguration(KeYRecoderExcHandler keh) {
        super(keh);
    }

    /** we need another factory for some new program elements */
    protected ProgramFactory makeProgramFactory() {
        return ProofJavaProgramFactory.getInstance();
    }

}
