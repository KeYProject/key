/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;

/**
 * Modification of {@link JavaCardDLStrategy} so that profiling data gets collected during strategy
 * run.
 */
class DataRecordingStrategy extends JavaCardDLStrategy {

    final FunctionPerformanceData computeCostData;
    final FunctionPerformanceData instantiateAppData;

    final DataRecordingTestFile dataRecordingTestFile;

    DataRecordingStrategy(Proof proof, DataRecordingTestFile dataRecordingTestFile) {
        super(proof, proof.getInitConfig().getSettings().getStrategySettings()
                .getActiveStrategyProperties());
        this.dataRecordingTestFile = dataRecordingTestFile;

        File computeCostDataDir = dataRecordingTestFile.getProfileDirectories().computeCostDataDir;
        computeCostData = new FunctionPerformanceData(computeCostDataDir, dataRecordingTestFile);

        File instantiateAppDataDir =
            dataRecordingTestFile.getProfileDirectories().instantiateAppDataDir;
        instantiateAppData =
            new FunctionPerformanceData(instantiateAppDataDir, dataRecordingTestFile);
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        long begin = System.nanoTime();
        RuleAppCost result = super.computeCost(app, pio, goal);
        long end = System.nanoTime();
        computeCostData.addDurationToData(app, goal, end - begin);
        return result;
    }

    @Override
    public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            RuleAppCostCollector collector) {
        long begin = System.nanoTime();
        super.instantiateApp(app, pio, goal, collector);
        long end = System.nanoTime();
        instantiateAppData.addDurationToData(app, goal, end - begin);
    }

    void saveCollectedData(long applyStrategyDuration) {
        computeCostData.updateData();
        instantiateAppData.updateData();
        RuleIndependentData.updateData(applyStrategyDuration, this);
    }

}
