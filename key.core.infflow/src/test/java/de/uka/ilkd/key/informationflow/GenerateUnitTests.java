/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow;

import de.uka.ilkd.key.proof.runallproofs.ProofCollections;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.TestFile;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static de.uka.ilkd.key.proof.runallproofs.GenerateUnitTests.*;

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
        var collections = List.of(InfFlowProofCollection.automaticInfFlow());
        if (args.length != 1) {
            System.err.println("Usage: <main> <output-folder>");
            System.exit(1);
        }
        var outputFolder = Paths.get(args[0]);
        run(outputFolder, collections);
    }
}