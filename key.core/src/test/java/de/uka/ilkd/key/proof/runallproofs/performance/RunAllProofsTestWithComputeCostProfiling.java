/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.IOException;
import java.util.Date;
import java.util.Objects;
import java.util.stream.Stream;

import de.uka.ilkd.key.proof.runallproofs.ProofCollections;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsFunctional;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;

import org.junit.jupiter.api.*;

/**
 * Same as {@link RunAllProofsFunctional} but we alter
 * {@link JavaCardDLStrategy#computeCost(de.uka.ilkd.key.rule.RuleApp, de.uka.ilkd.key.logic.PosInOccurrence, de.uka.ilkd.key.proof.Goal)}
 * so that statistical data about that method can be recorded (time duration, number of invocations
 * and potentially other stuff).
 */
@Tag("performance")
@Tag("owntest")
@Tag("slow")
public class RunAllProofsTestWithComputeCostProfiling {
    private static ProfilingDirectories directories;
    static File plotScript;

    /**
     * Note: This static initialisation block should only be executed once for each
     * {@link RunAllProofsTestWithComputeCostProfiling} run. This can easily be broken since fork
     * mode of runallproofs re-executes static initialisation blocks in each created subprocess. Be
     * aware of that in case you intend to change or move this block.
     */
    static void initDirectories(Date runStart) {
        directories = new ProfilingDirectories(runStart);
    }

    @TestFactory
    Stream<DynamicTest> data() throws Exception {
        ProofCollection proofCollection = ProofCollections.automaticJavaDL();
        // TODO weigl parseIndexFile("index/automaticJAVADL.txt", DataRecordingParser::new);
        proofCollection.getSettings().getStatisticsFile().setUp();
        initDirectories(proofCollection.getSettings().runStart);
        return RunAllProofsTest.data(proofCollection);
    }


    @BeforeAll
    public static void initPlotScriptLocation() {
        plotScript = new File("../scripts/tools/runAllProofs_createPerformancePlots/plot2png.sh");
        if (!plotScript.exists()) {
            throw new RuntimeException("Error: Script for plot creation not found!");
        }
    }

    @AfterAll
    public static void createPlots() throws IOException {
        createPlots(directories.computeCostDataDir);
        createPlots(directories.instantiateAppDataDir);
    }

    public static void createPlots(File dataDir) throws IOException {
        for (File ruleData : Objects.requireNonNull(dataDir.listFiles())) {
            String ruleName = ruleData.getAbsolutePath();
            // /.../rulename.data -> /.../rulename [remove file ending]
            ruleName = ruleName.substring(0, ruleName.length() - 5);

            // gnuplot -e "ruledatalocation=' /.../rulename'" plot2png.sh
            System.out.println("Plotting data for rule: " + ruleData.getName().split(".data")[0]);
            ProcessBuilder pb = new ProcessBuilder("gnuplot", "-e",
                "ruledatalocation='" + ruleName + "'", plotScript.getAbsolutePath());
            pb.inheritIO();
            try {
                pb.start().waitFor();
            } catch (InterruptedException e) {
                System.out.println("InterruptedException: " + e.getMessage());
            }
        }
    }
}
