package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.util.Properties;

/**
 * The purpose of this class is to write rule-independent data to the
 * filesystem, that is obtained from a {@link DataRecordingStrategy} run.
 */
public class RuleIndependentData {

    private static final String APPLY_STRATEGY_DURATION = "applyStrategyDuration";

    private final File ruleIndependentDataDir;

    private final File totalTimesFile;

    private final Properties totalTimesData = new Properties();

    private RuleIndependentData(ProfilingDirectories directories) {
        ruleIndependentDataDir = directories.ruleIndependentDataDir;
        totalTimesFile = new File(ruleIndependentDataDir, "totaltimes.properties");

        /*
         * Load previous totaltimes from filesystem.
         */
        if (totalTimesFile.exists()) {
            try (Reader r = new FileReader(totalTimesFile)) {
                totalTimesData.load(r);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
    }

    private long get(String key) {
        return Long.parseLong(totalTimesData.getProperty(key, 0 + ""));
    }

    private void add(String key, long l) {
        long value = get(key);
        value += l;
        totalTimesData.setProperty(key, value + "");
    }

    private void addTotalDurationAndInvocations(String functionName,
            FunctionPerformanceData data) {
        add(functionName + "Invocations", data.totalInvocations);
        add(functionName + "Duration", data.totalDuration);
    }

    private void updateDataOnFileSystem() {
        /*
         * Update duration percentage for functions computeCost() and
         * instantiateApp().
         */
        final int ccPercentage = updateFunctionPercentage("computeCost");
        final int iaPercentage = updateFunctionPercentage("instantiateApp");

        /*
         * Update data in file: ruleIndependentData.properties
         */
        try (FileOutputStream totalTimesOutputStream = new FileOutputStream(
                totalTimesFile)) {
            totalTimesData.store(totalTimesOutputStream,
                    "Performance Test Total Durations (and Invocations)");
        } catch (Exception e) {
            throw new RuntimeException(e);
        }

        /*
         * Update data in file: PercentageOverTime.data
         */
        File percentageOverTimeFile = new File(ruleIndependentDataDir, "PercentageOverTime.data");
        String[] columns = new String[] {
                "System.currentTimeMillis()", "computeCostPercentage",
                "instantiateAppPercentage" };
        String description = "Percentages of how much time computeCost() and instantiateApp() take "
                + "in overall applyStrategy() execution.";
        try (DataRecordingTable table = new DataRecordingTable(percentageOverTimeFile, columns, description)) {
            table.writeRow(System.currentTimeMillis(), ccPercentage, iaPercentage);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Computes how much time a profiled function takes from overall
     * applyStrategy() time.
     */
    private int updateFunctionPercentage(String functionName) {
        double a = get(functionName + "Duration");
        double b = get(APPLY_STRATEGY_DURATION);
        String key = functionName + "Duration_PERCENTAGE";
        int percentage = (int) (100 * a / b);
        totalTimesData.setProperty(key, percentage + "%");
        return percentage;
    }

    /**
     * Updates {@link RuleIndependentData} after by adding data obtained from
     * {@link DataRecordingStrategy}.
     */
    public static void updateData(long applyStrategyDuration,
            DataRecordingStrategy dataRecordingStrategy) {
        RuleIndependentData t = new RuleIndependentData(dataRecordingStrategy.dataRecordingTestFile.directories);

        t.add("applyStrategyInvocations", 1);
        t.add(APPLY_STRATEGY_DURATION, applyStrategyDuration);

        t.addTotalDurationAndInvocations("computeCost",
                dataRecordingStrategy.computeCostData);
        t.addTotalDurationAndInvocations("instantiateApp",
                dataRecordingStrategy.instantiateAppData);

        t.updateDataOnFileSystem();
    }

}
