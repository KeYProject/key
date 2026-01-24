/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.io.IOException;
import java.util.Date;

import de.uka.ilkd.key.proof.runallproofs.proofcollection.ForkMode;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollection;
import de.uka.ilkd.key.proof.runallproofs.proofcollection.ProofCollectionSettings;

import static de.uka.ilkd.key.proof.runallproofs.ProofCollections.loadFromFile;
import static org.assertj.core.api.Assertions.assertThat;

public class WdProofCollection {
    public static ProofCollection automaticWd() throws IOException {
        var settings = new ProofCollectionSettings(new Date());
        /*
         * Defines a base directory.
         * All paths in this file are treated relative to base directory (except path for base
         * directory itself).
         */
        settings.setBaseDirectory("../key.ui/examples/");

        /*
         * Defines a statistics file.
         * Path is relative to base directory.
         */
        settings.setStatisticsFile("build/reports/runallproofs/runStatistics.csv");

        /*
         * Fork mode setting, can be declared to create subprocesses while running tests declared in
         * this file.
         * Possible modes: noFork-all files are proven within a single process
         * pervar g = c.group("- one subprocess is created for each group
         * perFile-one subprocess is created for each file
         */
        settings.setForkMode(ForkMode.PERGROUP);

        /*
         * Enable or disable proof reloading.
         * If enabled, closed proofs will be saved and reloaded after prover is finished.
         */
        settings.setReloadEnabled(true);

        /*
         * Temporary directory, which is used for inter process communication when using forked
         * mode.
         * The given path is relative to baseDirectory.
         */
        settings.setTempDir("build/runallproofs_wd_tmp");

        /*
         * If the fork mode is not set to noFork, the launched subprocesses are terminated as
         * soon as the timeout specified here has elapsed. No timeout occurs if not specified.
         *
         * Timeout per subprocess in seconds
         */
        settings.setForkTimeout(2000);

        /*
         * If the fork mode is not set to noFork, the launched subprocesses
         * get the specified amount of heap memory.
         *
         * Heap memory for subprocesses (like 500m or 2G)
         */
        // forkMemory = 1000m

        /*
         * To run the forked JVM in debug mode, set the TCP port to listen to here.
         * You can prefix the port with "wait:" to make the JVM suspend till the
         * process has connected.
         *
         * Examples: forkDebugPort = "8000"
         * forkDebugPort = "wait:1234"
         */
        // forkDebugPort = "wait:1234"

        /*
         * By default, runAllProofs does not print a lot of information.
         * Set this to true to get more output.
         */
        settings.setVerboseOutput(true);
        // verboseOutput = true

        /*
         * By default, runAllProofs runs all groups in this file.
         * By naming a comma separated list of groups here, the
         * test can be restricted to these groups (for debugging).
         */
        // runOnlyOn = group1, group2 (the space after each comma is mandatory)
        // settings.setRunOnlyOn("performance, performancePOConstruction");

        settings.setKeySettings(loadFromFile("automaticJAVADL.properties"));


        // // Tests for information flow
        var c = new ProofCollection(settings);

        var g = c.group("wd_revarray");
        // g.notprovable("./firstTouch/05-ReverseArray/reverse2WD.key");
        g.provable("./firstTouch/05-ReverseArray/reverse2WD_Y.key");
        // g.notprovable("./firstTouch/06-BinarySearch/searchWD.key");
        // does not exists anymore
        // g.notprovable("./firstTouch/07-Cell/CellClient_mWD.key");
        // g.provable("./firstTouch/07-Cell/Cell_CellWD.key");
        // g.provable("./firstTouch/07-Cell/Cell_getXWD.key");
        // g.provable("./firstTouch/07-Cell/Cell_setXWD.key");

        g = c.group("wd_java5");
        g.provable("./firstTouch/08-Java5/For_infiniteLoopWD.key");
        // g.provable("./firstTouch/08-Java5/For_infiniteLoopWithWDLoop.key");
        g.provable("./firstTouch/08-Java5/For_invariantWD.key");
        g.provable("./firstTouch/08-Java5/For_sumWD.key");
        // g.notprovable("./firstTouch/08-Java5/For_sumWithWDLoop.key");

        g = c.group("wd_quicktour");
        g.provable("./firstTouch/09-Quicktour/CardException_getCauseWD.key");
        g.provable("./firstTouch/09-Quicktour/CardException_getMessageWD.key");
        g.provable("./firstTouch/09-Quicktour/CardException_initCauseWD.key");
        g.provable("./firstTouch/09-Quicktour/LogFile_LogFileWD.key");
        g.provable("./firstTouch/09-Quicktour/LogFile_LogFileWithWDLoop.key");
        g.provable("./firstTouch/09-Quicktour/LogFile_addRecordWD.key");
        g.provable("./firstTouch/09-Quicktour/LogFile_getMaximumRecordWD.key");
        g.provable("./firstTouch/09-Quicktour/LogFile_getMaximumRecordWithWDLoop.key");
        g.provable("./firstTouch/09-Quicktour/LogFile_invariantWD.key");
        g.provable("./firstTouch/09-Quicktour/LogRecord_getBalanceWD.key");
        g.provable("./firstTouch/09-Quicktour/LogRecord_getTransactionIdWD.key");
        g.provable("./firstTouch/09-Quicktour/LogRecord_invariantWD.key");
        g.provable("./firstTouch/09-Quicktour/LogRecord_setRecordWD.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_PayCardWD.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_PayCardintWD.key");
        g.provable("./firstTouch/09-Quicktour/PayCard__chargeExcWD.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_chargeAndRecordWD.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_chargeWD.0.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_chargeWD.1.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_createJuniorCardWD.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_invariantWD.key");
        g.provable("./firstTouch/09-Quicktour/PayCard_isValidWD.key");

        g = c.group("wd_sita");
        g.provable("./firstTouch/10-SITA/SITA3_commonEntryWD.key");
        g.provable("./firstTouch/10-SITA/SITA3_commonEntryWithWDLoop.key");
        g.provable("./firstTouch/10-SITA/SITA3_invariantWD.key");
        g.provable("./firstTouch/10-SITA/SITA3_rearrangeWD.key");
        g.provable("./firstTouch/10-SITA/SITA3_rearrangeWithWDLoop.key");
        g.provable("./firstTouch/10-SITA/SITA3_swapWD.key");

        g = c.group("wd_blockcontracts");
        // g.notprovable("./heap/block_contracts/GreatestCommonDivisor_ofWithWD.key");

        g = c.group("wd_fm12_01_LRS");
        // g.notprovable("./heap/fm12_01_LRS/LCP_lcpWD.key");
        // g.notprovable("./heap/fm12_01_LRS/LRS_doLRSWD.key");
        // g.notprovable("./heap/fm12_01_LRS/SuffixArray_invariantWD.key");
        // g.notprovable("./heap/fm12_02_PrefixSum/PrefixSumRec_minWD.key");

        g = c.group("wd_list");
        // g.notprovable("./heap/list_recursiveSpec/ListOperationsNonNull_getNextNNWD.key");
        // g.notprovable("./heap/list_seq/ArrayList_newArrayWD.key");
        g.provable("./heap/list_seq/ArrayList_newArrayWD_Y.key");
        // g.notprovable("./heap/list_seq/SimplifiedLinkedList_getNextWD.key");
        // g.notprovable("./heap/list_seq/SimplifiedLinkedList_invariantWD.key");
        // g.notprovable("./heap/list_seq/TestLists_appendWD.key");

        g = c.group("wd_otherheap");
        // g.notprovable("./heap/observer/ExampleSubject_valueWD.key");
        // g.notprovable("./heap/saddleback_search/Saddleback_searchWD.key");
        g.provable("./heap/saddleback_search/Saddleback_searchWithWDLoop.key");
        // g.notprovable("./heap/vacid0_01_SparseArray/Harness_sparseArrayTestHarness1WD.key");

        g = c.group("wd_vstte10_sam");
        g.provable("./heap/vstte10_01_SumAndMax/SumAndMax_sumAndMaxWD.key");
        g.provable("./heap/vstte10_01_SumAndMax/SumAndMax_sumAndMaxWithWDLoop.key");

        g = c.group("wd_vstte10_ll");
        g.provable("./heap/vstte10_03_LinkedList/Node_consWD.key");
        g.provable("./heap/vstte10_03_LinkedList/Node_invWD.key");
        g.provable("./heap/vstte10_03_LinkedList/Node_searchWD.key");


        g = c.group("wd_vstte10_queens");
        // g.notprovable("./heap/vstte10_04_Queens/Queens_nQueensWD.key");
        // g.notprovable("./heap/vstte10_04_Queens/Queens_searchWD.key");
        // g.notprovable("./heap/vstte10_05_Queue/LinkedList_tailWD.key");

        for (var testFile : g.getTestFiles()) {
            try {
                assertThat(testFile.getKeYFile())
                        .exists()
                        .content().contains("\\profile \"java-wd\";");
            } catch (AssertionError e) {
                System.err.println(testFile.getKeYFile());
                throw e;
            }
        }

        return c;
    }
}
