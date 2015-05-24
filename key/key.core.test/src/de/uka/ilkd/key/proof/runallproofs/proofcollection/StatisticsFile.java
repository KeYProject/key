package de.uka.ilkd.key.proof.runallproofs.proofcollection;

import java.io.File;
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
 */
public class StatisticsFile implements Serializable {

   private final File location;

   @SuppressWarnings("rawtypes")
   private static final Column[] columns = new Column[] {
         new Column<String>("Name", "---SUM---") {

            @Override
            String addEntry(Statistics statistics, File keyFile,
                  boolean proofClosed) {
               String name = keyFile.getAbsolutePath();
               final int slashIndex = name.lastIndexOf("examples/");
               return slashIndex >= 0 ? name.substring(slashIndex) : name;
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

         }, new Column<Integer>("Closed", 0) {

            @Override
            Integer addEntry(Statistics statistics, File keyFile, boolean closed) {
               int proofClosed = closed ? 1 : 0;
               sum += proofClosed;
               return proofClosed;
            }

         }, new Column<Double>("Time per step", 0.0) {

            @Override
            Double addEntry(Statistics statistics, File keyFile,
                  boolean proofClosed) {
               double value = statistics.timePerStepInNano / 1000000;
               sum += value;
               return value;
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
    * Is set false until method {@link #init()} has been called.
    */
   private boolean initialized = false;

   /**
    * Method for setting up statistics file. Deletes existing statistics file
    * (if one exists). Creates a new one and writes column names in first row of
    * table.
    */
   private void init() throws IOException {
      if (!initialized) {
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
         initialized = true;
      }
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
      init();
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
   public void close() throws IOException {
      init();
      List<String> sums = new LinkedList<>();
      for (Column<?> column : columns) {
         sums.add(column.sum.toString());
      }
      writeLine(sums);
   }

   /**
    * A column in statistics table whose entries are values of type {@link Long}
    * .
    */
   private abstract static class LongColumn extends Column<Long> {
      LongColumn(String name) {
         super(name, 0L);
      }

      @Override
      Long addEntry(Statistics statistics, File keyFile, boolean proofClosed) {
         long l = getLongValueFromStatistics(statistics);
         sum = sum + l;
         return l;
      }

      abstract long getLongValueFromStatistics(Statistics statistics);
   }

   /**
    * Objects of this class represent a column in statistics file. Type of
    * column entries is kept generic.
    */
   private abstract static class Column<T> {
      final String name;
      T sum;

      Column(String name, T sum) {
         this.name = name;
         this.sum = sum;
      }

      abstract T addEntry(Statistics statistics, File keyFile,
            boolean proofClosed);
   }

}
