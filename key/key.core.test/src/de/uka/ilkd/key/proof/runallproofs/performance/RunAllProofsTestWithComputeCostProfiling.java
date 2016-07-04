package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.IOException;
import java.util.Date;
import java.util.List;

import org.antlr.runtime.TokenStream;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uka.ilkd.key.proof.runallproofs.Function;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsDirectories;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsFunctional;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTestUnit;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionParser;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;

/**
 * Same as {@link RunAllProofsFunctional} but we alter
 * {@link JavaCardDLStrategy#computeCost(de.uka.ilkd.key.rule.RuleApp, de.uka.ilkd.key.logic.PosInOccurrence, de.uka.ilkd.key.proof.Goal)}
 * so that statistical data about that method can be recorded (time duration,
 * number of invocations and potentially other stuff).
 */
@RunWith(Parameterized.class)
public class RunAllProofsTestWithComputeCostProfiling extends RunAllProofsTest {

    private static ProfilingDirectories directories;

    /**
     * Note: This static initialisation block should only be executed once for
     * each {@link RunAllProofsTestWithComputeCostProfiling} run. This can
     * easily be broken since fork mode of runallproofs re-executes static
     * initialisation blocks in each created subprocess. Be aware of that in
     * case you intend to change or move this block.
     */
    static void initDirectories(Date runStart) {
        directories = new ProfilingDirectories(runStart);
    }

    public RunAllProofsTestWithComputeCostProfiling(RunAllProofsTestUnit unit) {
        super(unit);
    }

    @Parameters(name = "{0}")
    public static List<RunAllProofsTestUnit[]> data() throws Exception {
        ProofCollection proofCollection = parseIndexFile("index/automaticJAVADL.txt",
                new Function<TokenStream, ProofCollectionParser>() {
                    @Override
                    public ProofCollectionParser apply(TokenStream t) {
                        return new DataRecordingParser(t);
                    }
                });
        proofCollection.getSettings().getStatisticsFile().setUp();
        initDirectories(proofCollection.getSettings().runStart);
        return data(proofCollection);
    }

    static File plotScript;

    @BeforeClass
    public static void initPlotScriptLocation() throws IOException {
        plotScript = new File(RunAllProofsDirectories.KEY_HOME
                + File.separator + "scripts"
                + File.separator + "tools"
                + File.separator + "runAllProofs_createPerformancePlots"
                + File.separator + "plot2png.sh");
        if (!plotScript.exists()) {
            throw new RuntimeException("Error: Script for plot creation not found!");
        }
    }

    @AfterClass
    public static void createPlots() throws IOException {
        createPlots(directories.computeCostDataDir);
        createPlots(directories.instantiateAppDataDir);
    }

    public static void createPlots(File dataDir) throws IOException {
        for (File ruleData : dataDir.listFiles()) {
            String ruleName = ruleData.getAbsolutePath();
            // /.../rulename.data -> /.../rulename [remove file ending]
            ruleName = ruleName.substring(0, ruleName.length() - 5);

            // gnuplot -e "ruledatalocation=' /.../rulename'" plot2png.sh
            System.out.println("Plotting data for rule: " + ruleData.getName().split(".data")[0]);
            ProcessBuilder pb = new ProcessBuilder("gnuplot", "-e", "ruledatalocation='" + ruleName + "'",
                    plotScript.getAbsolutePath());
            pb.inheritIO();
            try {
                pb.start().waitFor();
            } catch (InterruptedException e) {
                System.out.println("InterruptedException: " + e.getMessage());
            }
        }
    }

}
