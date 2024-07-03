/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.proof.runallproofs.performance;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestProperty;

import org.antlr.runtime.TokenStream;

public class DataRecordingParser extends ProofCollectionParser {

    public DataRecordingParser(TokenStream input) {
        super(input);
    }

    @Override
    public DataRecordingTestFile getTestFile(TestProperty testProperty, String path,
            ProofCollectionSettings settings) {
        return new DataRecordingTestFile(testProperty, path, settings);
    }
}
