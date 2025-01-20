/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.IOException;
import java.util.Collections;

import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;

/**
 * A {@link ProofCollectionUnit} that is created from a single {@link TestFile} that is not declared
 * as part of a group.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class SingletonProofCollectionUnit extends ProofCollectionUnit {

    private static final long serialVersionUID = 1L;
    private final TestFile file;
    private final ProofCollectionSettings settings;

    public SingletonProofCollectionUnit(TestFile testFile, ProofCollectionSettings settings) {
        this.file = testFile;
        this.settings = settings;
    }

    @Override
    public RunAllProofsTestUnit createRunAllProofsTestUnit(String testName) throws IOException {
        return new RunAllProofsTestUnit(testName, settings, Collections.singletonList(file), true);
    }

    @Override
    String getName() throws IOException {
        return file.getKeYFile().getName();
    }

}
