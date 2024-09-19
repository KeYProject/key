/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.io.IOException;
import java.util.Date;

public class ProofCollections {
    public static ProofCollection automaticRustyDL() throws IOException {
        var settings = new ProofCollectionSettings(new Date());

        /*
         * Defines a base directory.
         * All paths in this file are treated relative to base directory (except path for base
         * directory itself).
         */
        settings.setBaseDirectory("src/test/resources/testcase/examples");

        /*
         * Defines a statistics file.
         * Path is relative to base directory.
         */
        settings.setStatisticsFile("build/reports/runallproofs/runStatistics.csv");

        /*
         * Enable or disable proof reloading.
         * If enabled, closed proofs will be saved and reloaded after prover is finished.
         */
        settings.setReloadEnabled(true);

        /*
         * By default, runAllProofs does not print a lot of information.
         * Set this to true to get more output.
         */
        settings.setVerboseOutput(true);

        var c = new ProofCollection(settings);
        var simple = c.group("simple");
        simple.loadable("simple.proof");
        simple.loadable("if.proof");

        return c;
    }
}
