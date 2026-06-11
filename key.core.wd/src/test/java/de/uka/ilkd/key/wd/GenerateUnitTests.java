/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.List;

import de.uka.ilkd.key.proof.runallproofs.GenerateUnitTestsUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Generation of test cases (JUnit) for given proof collection files.
 * <p>
 * This class is intended to be called from gradle. See the gradle task
 * {@code generateRunAllProofs}.
 * <p>
 * The considered proof collections files are configured statically in
 * {@link ProofCollections}.
 *
 * @author Alexander Weigl
 * @version 1 (6/14/20)
 */
public class GenerateUnitTests {
    private static final Logger LOGGER = LoggerFactory.getLogger(GenerateUnitTests.class);

    public static void main(String[] args) throws IOException {
        var collections = List.of(WdProofCollection.automaticWd());
        if (args.length != 1) {
            System.err.println("Usage: <main> <output-folder>");
            System.exit(1);
        }
        var outputFolder = Paths.get(args[0]);
        GenerateUnitTestsUtil.run(outputFolder, collections);
    }
}
