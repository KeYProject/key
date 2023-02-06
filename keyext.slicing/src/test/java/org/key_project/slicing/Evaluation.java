package org.key_project.slicing;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.io.IntermediateProofReplayer;
import de.uka.ilkd.key.proof.io.ProblemLoaderControl;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.smt.RuleAppSMT;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;
import org.junit.Ignore;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;
import org.key_project.slicing.analysis.AnalysisResults;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;

@Tag("owntest")
class Evaluation {
    private static final Logger LOGGER = LoggerFactory.getLogger(Evaluation.class);

    public static final File testCaseDirectory =
        new File("/home/arne/Documents/KIT/BA/Evaluation/");

    // commented out file = doesn't load
    /* commented out file = already evaluated */
    private static final String[] FILES = new String[] {
        "01_Contraposition.proof",
        "02_Liarsville.proof",
        "03_AuntAgatha.proof",
        "04_TransitivityOfSubset.proof",
        "05_SumAndMax.zproof",
        "06_BinarySearch.zproof",
        "07_EnhancedFor.zproof",
        "08_RemoveDuplicates1.zproof",
        "08_RemoveDuplicates2.zproof",
        "08_RemoveDuplicates3.zproof",
        "09_SITA1.zproof",
        "09_SITA2.zproof",
        "09_SITA3.zproof",
        "10_SimpleArrayReversal.zproof",
        "11_PermutedSum_manual.zproof",
        "12_Quicksort_scripted.zproof",
        "13_quadraticInEq9_focused_goals.proof",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__capacity(int)).JML normal_behavior operation contract.0.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__capacity(int)).JML normal_behavior operation contract.1.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__capacity(int)).JML normal_behavior operation contract.2.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__init(int)).JML normal_behavior operation contract.0.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__isEmpty()).JML normal_behavior operation contract.0.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__maskNull(java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__nextKeyIndex(int,int)).JML normal_behavior operation contract.0.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__resize(int)).JML normal_behavior operation contract.1.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__size()).JML normal_behavior operation contract.0.proof.gz",
        "IdentityHashMap/01_KEY_IHM/KeY-proof-files/VerifiedIdentityHashMap/java.util.VerifiedIdentityHashMap(java.util.VerifiedIdentityHashMap__unmaskNull(java.lang.Object)).JML normal_behavior operation contract.0.proof.gz",
        "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__loop_body((I,int,int,int,int,int)).JML normal_behavior operation contract.0.proof",
        "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__move_great_left((I,int,int,int)).JML normal_behavior operation contract.0.proof",
        "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__move_great_left_in_loop((I,int,int,int,int)).JML normal_behavior operation contract.0.proof",
        "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__move_less_right((I,int,int,int)).JML normal_behavior operation contract.0.proof",
        "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__prepare_indices((I,int,int)).JML normal_behavior operation contract.0.proof",
        "DualPivot_KeY_Proofs/overflow/DualPivotQuicksort/DualPivotQuicksort(DualPivotQuicksort__sort((I)).JML normal_behavior operation contract.0.proof",

        "DualPivot_KeY_Proofs/permutation/SinglePivotPartition_perm/ThreeWayQs(ThreeWayQs__sort((I)).JML normal_behavior operation contract.0.proof",
        "DualPivot_KeY_Proofs/permutation/SwapValues_perm/move_great_left.proof",
        "DualPivot_KeY_Proofs/permutation/SwapValues_perm/move_less_right.proof",

        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/calcE.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/eInsertionSort_SavedAgain.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/loop_body.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/move_great_left.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/move_great_left_in_loop.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/move_less_right.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/prepare_indices.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/sort_I.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/sort_I_int_int.proof",
        "DualPivot_KeY_Proofs/sort/DualPivotQuicksort/split.proof",
        "DualPivot_KeY_Proofs/sort/SinglePivotPartition/sort_I.proof",
        "DualPivot_KeY_Proofs/sort/SwapValues/move_great_left.proof",
        "DualPivot_KeY_Proofs/sort/SwapValues/move_less_right.proof",
        "DualPivot_KeY_Proofs/sort/SwapValues/swap_values.proof",
    };
    // Sizes:
    // 8, 14, 51, 63, 77, 127, 148, 189,
    // 320, 373, 417, 430, 441, 489, 493, 540, 611, 643, 658, 892,
    // 1133, 1140, 1245, 1471, 1582, 1814, 1858, 1928,
    // 2092, 2112, 2120, 2298, 2349, 2477, 2793, 3041, 3862, 4556, 4671, 4999, 5380, 6049,
    // 11272, 20623, 21615, 47352, 54572, 64968,
    // 110512, 120960, 162348

    private long analyzeTime = 0;

    @Test
    @Ignore("used during evaluation")
    void loadAll() {
        // run with: -Xmx4096m
        long time1 = System.currentTimeMillis();
        loadAllOnce(true);
        long time2 = System.currentTimeMillis();
        loadAllOnce(true);
        long time3 = System.currentTimeMillis();
        LOGGER.info("Replay time: {} (warmup) {} (second iteration)", time2 - time1, time3 - time2);
        // without tracker: 264834 258437
        // with tracker: 271606 265942 (+3%)
    }

    @Test
    @Ignore("used during evaluation")
    void sliceEach() throws Exception {
        // run with: -Xmx4096m
        // warm up taclet index etc.
        loadProof("DualPivot_KeY_Proofs/sort/DualPivotQuicksort/eInsertionSort_SavedAgain.proof",
            true, false).first.dispose();
        PrintStream output = new PrintStream(new FileOutputStream("/tmp/log_dups.txt"));
        output.println(
            "Proof;Load time;Load time with tracker;Analyze time with marking;Analyze time;Slice time;Number of steps;Number of steps in slice;Branches;Branches in slice;Number of SMT goals;Number of SMT in slice");

        List<String> failures = new ArrayList<>();

        for (String filename : FILES) {
            LOGGER.info("loading {}", filename);
            int iterations = 1;
            for (int i = 0; i < iterations; i++) {
                long time1 = System.currentTimeMillis();

                Triple<KeYEnvironment<?>, Proof, DependencyTracker> proof1 =
                    loadProof(filename, false, false);
                if (!proof1.second.closed()) {
                    LOGGER.warn("proof not closed!");
                    proof1.first.dispose();
                    continue;
                }
                int origSize = proof1.second.countNodes();
                int origBranches = proof1.second.countBranches();
                long numberOfSMT =
                    proof1.second.allGoals().stream()
                            .filter(goal -> goal.node().getAppliedRuleApp() != null
                                    && goal.node().getAppliedRuleApp() instanceof RuleAppSMT)
                            .count();
                proof1.first.dispose();
                long time2 = System.currentTimeMillis();

                loadProof(filename, true, false).first.dispose();
                long time3 = System.currentTimeMillis();

                try {
                    Triple<Proof, DependencyTracker, AnalysisResults> result =
                        sliceProof(filename, false, true);
                    Proof proof2 = result.first;
                    int sliceSize = proof2.countNodes();
                    int sliceBranches = proof2.countBranches();
                    long numberOfSMT2 = proof2.allGoals().stream()
                            .filter(goal -> goal.node().getAppliedRuleApp() != null
                                    && goal.node().getAppliedRuleApp() instanceof RuleAppSMT)
                            .count();
                    proof2.dispose();
                    long time4 = System.currentTimeMillis();

                    Map<String, Long> timings = result.third.executionTime.executionTimesMap();
                    int pureAnalyze = 0;// timings.get(DependencyAnalyzer.DEPENDENCY_ANALYSIS2) +
                                        // timings.get(DependencyAnalyzer.DEPENDENCY_ANALYSIS3);
                    if (i < iterations - 1) {
                        System.err.printf("%s;%d;%d;%d;%d;%d;%d;%d;%d;%d;%d\n", filename,
                            time2 - time1, time3 - time2, analyzeTime, pureAnalyze, time4 - time3,
                            origSize, sliceSize, origBranches, sliceBranches, numberOfSMT,
                            numberOfSMT2);
                    } else {
                        output.printf("%s;%d;%d;%d;%d;%d;%d;%d;%d;%d;%d\n", filename, time2 - time1,
                            time3 - time2, analyzeTime, pureAnalyze, time4 - time3, origSize,
                            sliceSize, origBranches, sliceBranches, numberOfSMT, numberOfSMT2);
                    }
                } catch (Exception e) {
                    e.printStackTrace();
                    failures.add(filename);
                }
            }
        }
        output.flush();
        output.close();
        System.err.println("Failures:");
        for (String name : failures) {
            System.err.println(name);
        }
    }

    @Test
    @Ignore("used during evaluation")
    void sliceEachToFixedPoint() throws Exception {
        LOGGER.info("evaluating {} proofs", FILES.length);
        boolean depAnalysis = true;
        boolean dupAnalysis = false;
        GeneralSettings.noPruningClosed = false;
        // run with: -Xmx4096m
        PrintStream output =
            new PrintStream(new FileOutputStream("/tmp/log_fixedpoint_rework.txt"));
        output.println(
            "Proof;Load time;Load time with tracker;Analyze time;Slice time;Number of steps;Number of steps in slice;Branches;Branches in slice;Number of SMT goals;Number of SMT in slice");

        List<String> failures = new ArrayList<>();

        for (String filename : FILES) {
            LOGGER.info("loading {}", filename);
            Runtime runtime = Runtime.getRuntime();
            long total = runtime.totalMemory();
            long used = total - runtime.freeMemory();
            LOGGER.info("Java Heap Usage: {} MB / {} MB", used / 1024 / 1024, total / 1024 / 1024);
            long time1 = System.currentTimeMillis();

            Triple<KeYEnvironment<?>, Proof, DependencyTracker> proof1 =
                loadProof(filename, false, false);
            if (!proof1.second.closed()) {
                LOGGER.warn("proof not closed!");
                proof1.first.dispose();
                continue;
            }
            int origSize = proof1.second.countNodes();
            int origBranches = proof1.second.countBranches();
            long numberOfSMT = proof1.second.allGoals().stream()
                    .filter(goal -> goal.node().parent().getAppliedRuleApp() != null
                            && goal.node().parent().getAppliedRuleApp() instanceof RuleAppSMT)
                    .count();
            proof1.first.dispose();
            long time2 = System.currentTimeMillis();

            loadProof(filename, true, false).first.dispose();
            long time3 = System.currentTimeMillis();

            boolean furtherSliceUseful = true;
            try {
                Triple<Proof, DependencyTracker, AnalysisResults> pair =
                    sliceProof(filename, depAnalysis, dupAnalysis);
                while (furtherSliceUseful) {
                    Proof proof2 = pair.first;
                    int sliceSize = proof2.countNodes();
                    int sliceBranches = proof2.countBranches();
                    long numberOfSMT2 = proof2.allGoals().stream()
                            .filter(goal -> goal.node().getAppliedRuleApp() != null
                                    && goal.node().getAppliedRuleApp() instanceof RuleAppSMT)
                            .count();
                    AnalysisResults results = pair.second.analyze(depAnalysis, dupAnalysis);
                    furtherSliceUseful = results.totalSteps != results.usefulStepsNr;
                    long time4 = System.currentTimeMillis();
                    if (furtherSliceUseful) {
                        // slice proof with a headless LoaderControl to avoid countless UI redraws
                        ProblemLoaderControl control = new DefaultUserInterfaceControl();
                        File nextPath = SlicingProofReplayer
                                .constructSlicer(control, proof2, results, null).slice();
                        LOGGER.info("loading {}", nextPath);

                        Triple<KeYEnvironment<?>, Proof, DependencyTracker> nextProof =
                            loadProof(nextPath.toString(), true, true);
                        pair = new Triple<>(nextProof.second, nextProof.third, null);
                    }
                    proof2.dispose();

                    System.err.printf("%s;%d;%d;%d;%d;%d;%d;%d;%d;%d;%d\n", filename, time2 - time1,
                        time3 - time2, analyzeTime, time4 - time3, origSize, sliceSize,
                        origBranches, sliceBranches, numberOfSMT, numberOfSMT2);
                    output.printf("%s;%d;%d;%d;%d;%d;%d;%d;%d;%d;%d\n", filename, time2 - time1,
                        time3 - time2, analyzeTime, time4 - time3, origSize, sliceSize,
                        origBranches, sliceBranches, numberOfSMT, numberOfSMT2);
                }
            } catch (Exception e) {
                e.printStackTrace();
                failures.add(filename);
            }
        }
        output.flush();
        output.close();
        System.err.println("Failures:");
        for (String name : failures) {
            System.err.println(name);
        }
    }

    @Test
    @Ignore("used during evaluation")
    void loadAndSliceAll() throws Exception {
        GeneralSettings.noPruningClosed = false;
        // run with: -Xmx4096m
        long time1 = System.currentTimeMillis();
        sliceAllOnce();
        long time2 = System.currentTimeMillis();
        sliceAllOnce();
        long time3 = System.currentTimeMillis();
        LOGGER.info("Replay + Slice + Replay time: {} (warmup) {} (second iteration)",
            time2 - time1, time3 - time2);
        // 338322 331194
    }

    private void sliceAllOnce() throws Exception {
        List<String> failures = new ArrayList<>();
        List<Pair<Integer, Integer>> sizes = new ArrayList<>();
        for (String filename : FILES) {
            LOGGER.info("Loading {}", filename);
            Triple<KeYEnvironment<?>, Proof, DependencyTracker> result =
                loadProof(filename, true, false);
            try {
                if (!result.first.getReplayResult().hasErrors()
                        && result.first.getReplayResult().getStatus()
                                .equals(IntermediateProofReplayer.SMT_NOT_RUN)) {
                    LOGGER.info("skipping"); // TODO: mark the open goals as "closable by SMT"?
                    result.first.dispose();
                    continue;
                }
                int originalSize = result.second.countNodes();
                DependencyTracker tracker = result.third;
                // analyze proof
                AnalysisResults results = tracker.analyze(true, false);
                // slice proof
                DefaultUserInterfaceControl control = new DefaultUserInterfaceControl();
                SlicingProofReplayer slicer = SlicingProofReplayer.constructSlicer(control,
                    result.second, results, control);
                File tempFile = slicer.slice();

                KeYEnvironment<?> loadedEnvironment =
                    KeYEnvironment.load(JavaProfile.getDefaultInstance(), tempFile, null,
                        null, null, null, null, null, true);
                try {
                    Proof slicedProof = loadedEnvironment.getLoadedProof();

                    Assertions.assertTrue(slicedProof.closed());

                    Files.delete(tempFile.toPath());

                    int slicedSize = slicedProof.countNodes();
                    sizes.add(new Pair<>(originalSize, slicedSize));
                } finally {
                    loadedEnvironment.dispose();
                }
            } catch (Exception e) {
                e.printStackTrace();
                failures.add(filename);
            } finally {
                result.first.dispose();
            }
        }
        if (!failures.isEmpty()) {
            LOGGER.info("Failures:");
            for (String filename : failures) {
                LOGGER.info("{}", filename);
            }
        }
        sizes.sort(Comparator.comparing(it -> it.first));
        for (var s : sizes) {
            System.out.printf("%s,%s\n", s.first, s.second);
        }
    }

    private void loadAllOnce(boolean withTracker) {
        var working = 0;
        var total = 0;
        var failures = new ArrayList<>();
        var sizes = new ArrayList<Integer>();
        for (var filename : FILES) {
            LOGGER.info("Loading {}", filename);
            var loadedCorrectly = false;
            total++;
            try {
                var result = loadProof(filename, withTracker, false);
                if (result != null) {
                    if (result.second.closed()
                            || (!result.first.getReplayResult().hasErrors()
                                    && result.first.getReplayResult().getStatus()
                                            .equals(IntermediateProofReplayer.SMT_NOT_RUN))) {
                        // NOTE: this assumes that such a status means it loaded successfully
                        // (i.e. setting up Z3 correctly would close the proof!)
                        loadedCorrectly = true;
                        sizes.add(result.second.countNodes());
                    }
                    result.first.dispose();
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
            if (loadedCorrectly) {
                working++;
            } else {
                failures.add(filename);
            }
        }
        LOGGER.info("Loaded {}/{} proofs", working, total);
        sizes.sort(Comparator.naturalOrder());
        LOGGER.info("Sizes: {}", Arrays.toString(sizes.toArray()));
        if (working != total) {
            LOGGER.info("Failures:");
            for (var filename : failures) {
                LOGGER.info("{}", filename);
            }
        }
    }

    private Triple<KeYEnvironment<?>, Proof, DependencyTracker> loadProof(String filename,
            boolean withTracker, boolean literalName) throws Exception {
        // load proof
        File proofFile = literalName ? new File(filename) : new File(testCaseDirectory, filename);
        Assertions.assertTrue(proofFile.exists());
        AtomicReference<DependencyTracker> tracker = new AtomicReference<>();
        KeYEnvironment<?> environment = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
            proofFile, null, null, null, null, null,
            withTracker ? proof -> {
                tracker.set(new DependencyTracker(proof));
            } : null, true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);

            return new Triple<>(environment, proof, tracker.get());
        } catch (Exception e) {
            environment.dispose();
            throw e;
        }
    }

    private Triple<Proof, DependencyTracker, AnalysisResults> sliceProof(String filename,
            boolean doDependencyAnalysis, boolean doDeduplicateRuleApps) throws Exception {
        boolean oldValue = GeneralSettings.noPruningClosed;
        GeneralSettings.noPruningClosed = false;
        // load proof
        File proofFile = new File(testCaseDirectory, filename);
        Assertions.assertTrue(proofFile.exists());
        AtomicReference<DependencyTracker> tracker = new AtomicReference<>();
        KeYEnvironment<?> environment =
            KeYEnvironment.load(JavaProfile.getDefaultInstance(), proofFile, null, null, null, null,
                null, proof -> {
                    tracker.set(new DependencyTracker(proof));
                }, true);
        try {
            // get loaded proof
            Proof proof = environment.getLoadedProof();
            Assertions.assertNotNull(proof);
            if (!proof.closed()) {
                throw new IllegalStateException("loaded proof not closed");
            }
            // analyze proof
            var time1 = System.currentTimeMillis();
            var results = tracker.get().analyze(doDependencyAnalysis, doDeduplicateRuleApps);
            analyzeTime = System.currentTimeMillis() - time1;
            // slice proof
            var control = new DefaultUserInterfaceControl();
            var slicer = SlicingProofReplayer.constructSlicer(control,
                proof, results, control);
            File path = slicer.slice();
            AtomicReference<DependencyTracker> tracker2 = new AtomicReference<>();
            KeYEnvironment<DefaultUserInterfaceControl> env2 =
                KeYEnvironment.load(JavaProfile.getDefaultInstance(), path, null,
                    null, null, null, null, proof1 -> {
                        tracker2.set(new DependencyTracker(proof1));
                    }, true);
            Proof slicedProof = env2.getLoadedProof();

            if (!slicedProof.closed()) {
                throw new IllegalStateException("sliced proof not closed!");
            }

            // Files.delete(tempFile);

            return new Triple<>(slicedProof, tracker2.get(), results);
        } finally {
            environment.dispose();
            GeneralSettings.noPruningClosed = oldValue;
        }
    }
}
