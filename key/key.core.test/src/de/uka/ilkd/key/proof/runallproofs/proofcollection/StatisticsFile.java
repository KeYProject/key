package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;

/**
 * Class for managing a file which contains statistics recorded during a
 * {@link RunAllProofsTest} run. Statistics are recorded as a table, which
 * contains one line for each tested file.
 * 
 * This class must be immutable because it is part of
 * {@link ProofCollectionSettings}, which is immutable as well.
 */
public class StatisticsFile implements Serializable {

   private final File location;

   @SuppressWarnings("rawtypes")
   private static final Column[] columns = new Column[] {
         new Column<String>("Name") {

            @Override
            String addEntry(Statistics statistics, File keyFile,
                  boolean proofClosed) {
               String name = keyFile.getAbsolutePath();
               final int slashIndex = name.lastIndexOf("examples/");
               return slashIndex >= 0 ? name.substring(slashIndex) : name;
            }

            @Override
            String computeSum(List<String> list) {
               return "---SUM---";
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

         }, new LongColumn("Overall time") {

            @Override
            long getLongValueFromStatistics(Statistics statistics) {
               return statistics.timeInNano / 1000000;
            }

         }, new LongColumn("Automode time") {

            @Override
            long getLongValueFromStatistics(Statistics statistics) {
               return statistics.autoModeTimeInNano / 1000000;
            }

         }, new Column<Integer>("Closed") {

            @Override
            Integer addEntry(Statistics statistics, File keyFile, boolean closed) {
               int proofClosed = closed ? 1 : 0;
               return proofClosed;
            }

            @Override
            String computeSum(List<String> list) {
               long ret = 0;
               for (String s : list) {
                  ret += Long.parseLong(s);
               }
               return "" + ret;
            }

         }, new Column<Double>("Time per step") {

            @Override
            Double addEntry(Statistics statistics, File keyFile,
                  boolean proofClosed) {
               double value = statistics.timePerStepInNano / 1000000;
               return value;
            }

            @Override
            String computeSum(List<String> list) {
               double ret = 0.0;
               for (String s : list) {
                  ret += Double.parseDouble(s);
               }
               return "" + ret;
            }

         }, new LongColumn("Total Runtime Memory") {

            @Override
            long getLongValueFromStatistics(Statistics statistics) {
               // get current memory consumption (after GC) in kB
               Runtime.getRuntime().gc();
               final long memory = (Runtime.getRuntime().totalMemory() - Runtime
                     .getRuntime().freeMemory()) / 1024;
               return memory;
            }

         } };

   public StatisticsFile(File location) {
      this.location = location;
   }

   /**
    * Deletes an old statistics file and sets up a new one that has column names
    * as first row.
    */
   public void setUp() throws IOException {
      // Create parent directory if it does not exist yet.
      if (!location.getParentFile().exists()) {
         location.getParentFile().mkdirs();
      }

      // Delete old statistics file if it exists already.
      if (location.exists()) {
         System.out.println("Deleting old RunAllProofs statistics file: "
               + location);
         location.delete();
      }

      // Write column names in the first line of statistics file.
      List<String> columnNames = new LinkedList<>();
      for (Column<?> column : columns) {
         columnNames.add(column.name);
      }
      writeLine(columnNames);
   }

   /**
    * Method used for writing a new line into the table of statistics entries.
    * 
    * @param entries
    *           List representing a line in the table. Each list entry
    *           corresponds to one table cell.
    * @throws IOException
    *            In case statistics file is not accessible for some reason.
    */
   private void writeLine(List<String> entries) throws IOException {
      final FileWriter statisticsFileWriter = new FileWriter(location, true);
      final PrintWriter statPrinter = new PrintWriter(statisticsFileWriter);
      String line = "";
      boolean first = true;
      for (String entry : entries) {
         line += first ? "" : "|";
         line += entry;
         first = false;
      }
      statPrinter.println(line);
      statPrinter.close();
      statisticsFileWriter.close();
   }

   /**
    * Append statistics for one proof to statistics file.
    * 
    * @param proof
    *           {@link Proof}, whose statistics will be added.
    * @param keyFile
    *           KeY file, from which the original proof obligation has been
    *           created, must be mentioned explicitly.
    * @throws IOException
    *            Thrown in case statistics file is not accessible.
    */
   public void appendStatistics(Proof proof, File keyFile) throws IOException {
      Statistics statistics = proof.getStatistics();
      boolean proofClosed = proof.closed();
      List<String> entries = new LinkedList<>();
      for (Column<?> column : columns) {
         entries.add(column.addEntry(statistics, keyFile, proofClosed)
               .toString());
      }
      writeLine(entries);
   }

   /**
    * Print sum for each column as last line when closing statistics file.
    */
   public void computeSums() throws IOException {
      try (BufferedReader br = new BufferedReader(new FileReader(location))) {
         // strip first line containing column names
         br.readLine();

         // Convert statistics table into an array of lists.
         @SuppressWarnings("unchecked")
         List<String>[] lists = new List[columns.length];
         for (int i = 0; i < lists.length; i++) {
            lists[i] = new LinkedList<String>();
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

         // write line of sums into statistics file
         List<String> entries = new LinkedList<>();
         int i = 0;
         for (Column<?> column : columns) {
            entries.add(column.computeSum(lists[i]));
            i++;
         }
         writeLine(entries);
      }
   }

   /**
    * A column in statistics table whose entries are values of type {@link Long}
    * .
    */
   private abstract static class LongColumn extends Column<Long> {
      LongColumn(String name) {
         super(name);
      }

      @Override
      Long addEntry(Statistics statistics, File keyFile, boolean proofClosed) {
         long l = getLongValueFromStatistics(statistics);
         return l;
      }

      @Override
      String computeSum(List<String> list) {
         long ret = 0;
         for (String s : list) {
            ret += Long.parseLong(s);
         }
         return "" + ret;
      }

      abstract long getLongValueFromStatistics(Statistics statistics);
   }

   /**
    * Objects of this class represent a column in statistics file. Type of
    * column entries is kept generic.
    */
   private abstract static class Column<T> {
      final String name;

      Column(String name) {
         this.name = name;
      }

      abstract String computeSum(List<String> list);

      abstract T addEntry(Statistics statistics, File keyFile,
            boolean proofClosed);
   }

}
