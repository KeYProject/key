/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.runallproofs.RunAllProofsTest;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Class for managing a file which contains statistics recorded during a {@link RunAllProofsTest}
 * run. Statistics are recorded as a table, which contains one line for each tested file.
 * <p>
 * This class must be immutable because it is part of {@link ProofCollectionSettings}, which is
 * immutable as well.
 */
public class StatisticsFile implements Serializable {
    private static final Logger LOGGER = LoggerFactory.getLogger(StatisticsFile.class);
    private final File statisticsFile;

    @SuppressWarnings("rawtypes")
    private static final Column[] columns = new Column[] { new Column<String>("Name") {
        @Override
        String addEntry(Statistics statistics, File keyFile, boolean proofClosed) {
            String name = keyFile.getAbsolutePath();
            final int slashIndex = name.lastIndexOf("examples/");
            return slashIndex >= 0 ? name.substring(slashIndex) : name;
        }

        @Override
        String[] computeSumAndAverage(List<String> list) {
            return new String[] { "---SUM---", "---AVG---" };
        }

    }, new LongColumn("Total rule apps") {

        @Override
        long getLongValueFromStatistics(Statistics statistics) {
            return statistics.totalRuleApps;
        }

    }, new LongColumn("Nodes") {

        @Override
        long getLongValueFromStatistics(Statistics statistics) {
            return statistics.nodes;
        }

    }, new LongColumn("Branches") {

        @Override
        long getLongValueFromStatistics(Statistics statistics) {
            return statistics.branches;
        }

    }, new LongColumn("Overall time (ms)") {

        @Override
        long getLongValueFromStatistics(Statistics statistics) {
            return statistics.timeInMillis;
        }

    }, new LongColumn("Automode time (ms)") {

        @Override
        long getLongValueFromStatistics(Statistics statistics) {
            return statistics.autoModeTimeInMillis;
        }

    }, new Column<Integer>("Closed") {

        @Override
        Integer addEntry(Statistics statistics, File keyFile, boolean closed) {
            return closed ? 1 : 0;
        }

        @Override
        String[] computeSumAndAverage(List<String> list) {
            long sum = 0;
            for (String s : list) {
                sum += Long.parseLong(s);
            }
            double avg = ((double) sum) / ((double) list.size());
            return new String[] { "" + sum, "" + avg };
        }

    }, new Column<Double>("Time per step (ms)") {

        @Override
        Double addEntry(Statistics statistics, File keyFile, boolean proofClosed) {
            return (double) statistics.timePerStepInMillis;
        }

        @Override
        String[] computeSumAndAverage(List<String> list) {
            double sum = 0.0;
            for (String s : list) {
                sum += Double.parseDouble(s);
            }
            double avg = sum / ((double) list.size());
            return new String[] { "" + sum, "" + avg };
        }

    }, new LongColumn("Total Runtime Memory (kB)") {

        @Override
        long getLongValueFromStatistics(Statistics statistics) {
            // get current memory consumption (after GC) in kB
            Runtime.getRuntime().gc();
            return (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()) / 1024;
        }

    } };

    public StatisticsFile(File location) {
        this.statisticsFile = location;
    }


    /**
     * Deletes an old statistics file and sets up a new one that has column names as first row.
     */
    public void setUp() throws IOException {
        setUp(true);
    }

    public void setUp(boolean delete) throws IOException {
        boolean printHeader = !statisticsFile.exists();

        // Create parent directory if it does not exist yet.
        if (!statisticsFile.getParentFile().exists()) {
            statisticsFile.getParentFile().mkdirs();
        }

        // Delete old statistics file if it exists already.
        if (delete && statisticsFile.exists()) {
            LOGGER.warn("Deleting old RunAllProofs statistics file: " + statisticsFile);
            statisticsFile.delete();
            printHeader = true;
        }

        if (printHeader) {
            // Write column names in the first line of statistics file.
            List<String> columnNames = new LinkedList<>();
            for (Column<?> column : columns) {
                columnNames.add(column.name);
            }
            writeLine(columnNames);
        }
    }

    /**
     * Method used for writing a new line into the table of statistics entries.
     *
     * @param entries List representing a line in the table. Each list entry corresponds to one
     *        table cell.
     * @throws IOException In case statistics file is not accessible for some reason.
     */
    private void writeLine(List<String> entries) throws IOException {
        final FileWriter statisticsFileWriter =
            new FileWriter(statisticsFile, StandardCharsets.UTF_8, true);
        final PrintWriter statPrinter = new PrintWriter(statisticsFileWriter);
        StringBuilder line = new StringBuilder();
        boolean first = true;
        for (String entry : entries) {
            line.append(first ? "" : "|");
            line.append(entry);
            first = false;
        }
        statPrinter.println(line);
        statPrinter.close();
        statisticsFileWriter.close();
    }

    /**
     * Append statistics for one proof to statistics file.
     *
     * @param proof {@link Proof}, whose statistics will be added.
     * @param keyFile KeY file, from which the original proof obligation has been created, must be
     *        mentioned explicitly.
     * @throws IOException Thrown in case statistics file is not accessible.
     */
    public void appendStatistics(Proof proof, File keyFile) throws IOException {
        Statistics statistics = proof.getStatistics();
        boolean proofClosed = proof.closed();
        List<String> entries = new LinkedList<>();
        for (Column<?> column : columns) {
            entries.add(column.addEntry(statistics, keyFile, proofClosed).toString());
        }
        writeLine(entries);
    }

    /**
     * Print sum for each column as last line when closing statistics file.
     */
    public void computeSumsAndAverages() throws IOException {
        try (BufferedReader br =
            new BufferedReader(new FileReader(statisticsFile, StandardCharsets.UTF_8))) {
            // strip first line containing column names
            br.readLine();

            // Convert statistics table into an array of lists.
            @SuppressWarnings("unchecked")
            List<String>[] lists = new List[columns.length];
            for (int i = 0; i < lists.length; i++) {
                lists[i] = new LinkedList<>();
            }
            for (String row; (row = br.readLine()) != null;) {
                String[] column = row.split("\\|");
                if (column.length != columns.length) {
                    throw new RuntimeException(
                        "Wrong number of columns after parsing statistics table.");
                }
                for (int i = 0; i < lists.length; i++) {
                    lists[i].add(column[i]);
                }
            }

            /*
             * Compute sums and averages.
             */
            List<String> sums = new LinkedList<>();
            sums.add("---SUM---");
            List<String> avgs = new LinkedList<>();
            avgs.add("---AVG---");
            for (int i = 1 /* Omit first column. */; i < columns.length; i++) {
                Column<?> column = columns[i];
                String[] sumAndAverage = column.computeSumAndAverage(lists[i]);
                assert sumAndAverage.length == 2
                        : "Expecting exactly 2 strings returned by computeSumAndAverage()";
                sums.add(sumAndAverage[0]);
                if (i != 6) {
                    avgs.add(sumAndAverage[1]);
                } else {
                    /*
                     * Adjust average calculation for "Time per step" so that it is more stable.
                     * (see bug #1442)
                     */
                    int sumNodes = Integer.parseInt(sums.get(1));
                    int sumAutomodeTime = Integer.parseInt(sums.get(4));
                    // In case sumNodes equals zero return the sum w/o dividing
                    if (sumNodes == 0) {
                        // It may be 0 if all files are "loadable".
                        avgs.add(Integer.toString(sumAutomodeTime));
                    } else {
                        avgs.add(Integer.toString(sumAutomodeTime / sumNodes));
                    }
                }
            }
            // Append lines of sums and averages to statistics file.
            writeLine(sums);
            writeLine(avgs);

            /*
             * Create *.sum.properties and *.avg.properties files for Jenkins.
             */
            String jobName = System.getenv("JOB_NAME");
            if (jobName == null) {
                jobName = "local";
            }
            String url =
                "URL=http://hudson.se.informatik.tu-darmstadt.de/userContent/statistics-" + jobName;
            File statisticsDir = statisticsFile.getParentFile();
            for (int i = 1 /* Omit first column. */; i < columns.length; i++) {

                // Create *.sum.properties file
                Path sumFile =
                    new File(statisticsDir, columns[i].name + ".sum.properties").toPath();
                String[] lines = new String[] { "YVALUE=" + sums.get(i), url };
                Files.write(sumFile, Arrays.asList(lines), Charset.defaultCharset());
                LOGGER.info("{} is written", sumFile);

                // Create *.avg.properties file
                Path avgFile =
                    new File(statisticsDir, columns[i].name + ".avg.properties").toPath();
                lines = new String[] { "YVALUE=" + avgs.get(i), url };
                Files.write(avgFile, Arrays.asList(lines), Charset.defaultCharset());
                LOGGER.info("{} is written", avgFile);

            }

            /*
             * Create properties file for number of test files.
             */
            int countFiles = lists[0].size();
            Path countFilesPath = new File(statisticsDir, "NumberTestFiles.properties").toPath();
            String[] lines = new String[] { "YVALUE=" + countFiles, url };
            Files.write(countFilesPath, Arrays.asList(lines), Charset.defaultCharset());
            LOGGER.info("{} is written", countFilesPath);
        }
    }


    /**
     * A column in statistics table whose entries are values of type {@link Long} .
     */
    private abstract static class LongColumn extends Column<Long> {
        LongColumn(String name) {
            super(name);
        }

        @Override
        Long addEntry(Statistics statistics, File keyFile, boolean proofClosed) {
            return getLongValueFromStatistics(statistics);
        }

        @Override
        String[] computeSumAndAverage(List<String> list) {
            long sum = 0;
            for (String s : list) {
                sum += Long.parseLong(s);
            }
            double avg = ((double) sum) / ((double) list.size());
            return new String[] { "" + sum, "" + avg };
        }

        abstract long getLongValueFromStatistics(Statistics statistics);
    }

    /**
     * Objects of this class represent a column in statistics file. Type of column entries is kept
     * generic.
     */
    private abstract static class Column<T> {
        final String name;

        Column(String name) {
            this.name = name;
        }

        abstract String[] computeSumAndAverage(List<String> list);

        abstract T addEntry(Statistics statistics, File keyFile, boolean proofClosed);
    }

    public File getStatisticsFile() {
        return statisticsFile;
    }
}
