package org.key_project.key4eclipse.resources.log;

import org.eclipse.core.runtime.Assert;

/**
 * A log recored managed by the {@link LogManager}.
 * @author Martin Hentschel
 */
public class LogRecord {
   /**
    * The kind.
    */
   private final LogRecordKind kind;
   
   /**
    * The start.
    */
   private final long start;
   
   /**
    * The duration.
    */
   private final long duration;
   
   /**
    * Only required proofs?
    */
   private final boolean onlyRequiredProofs;
   
   /**
    * Multi threading enabled?
    */
   private final boolean enableThreading;
   
   /**
    * The number of threads.
    */
   private final int numberOfThreads;

   /**
    * Constructor.
    * @param kind The kind.
    * @param start The start.
    * @param duration The duration.
    * @param onlyRequiredProofs Only required proofs?
    * @param enableThreading Multi threading enabled?
    * @param numberOfThreads The number of threads.
    */
   public LogRecord(LogRecordKind kind, 
                    long start, 
                    long duration, 
                    boolean onlyRequiredProofs, 
                    boolean enableThreading, 
                    int numberOfThreads) {
      Assert.isNotNull(kind);
      this.kind = kind;
      this.start = start;
      this.duration = duration;
      this.onlyRequiredProofs = onlyRequiredProofs;
      this.enableThreading = enableThreading;
      this.numberOfThreads = numberOfThreads;
   }

   /**
    * Returns the kind.
    * @return The kind.
    */
   public LogRecordKind getKind() {
      return kind;
   }

   /**
    * Returns the start.
    * @return The start.
    */
   public long getStart() {
      return start;
   }

   /**
    * Returns the duration.
    * @return The duration.
    */
   public long getDuration() {
      return duration;
   }

   /**
    * Returns only required proofs?
    * @return Only required proofs?
    */
   public boolean isOnlyRequiredProofs() {
      return onlyRequiredProofs;
   }

   /**
    * Returns multi threading enabled?
    * @return Multi threading enabled?
    */
   public boolean isEnableThreading() {
      return enableThreading;
   }

   /**
    * Returns the number of threads.
    * @return The number of threads.
    */
   public int getNumberOfThreads() {
      return numberOfThreads;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int hashCode() {
      int hashcode = 5;
      hashcode = hashcode * 17 + (int)duration;
      hashcode = hashcode * 17 + (enableThreading ? 1 : 0);
      hashcode = hashcode * 17 + kind.hashCode();
      hashcode = hashcode * 17 + numberOfThreads;
      hashcode = hashcode * 17 + (onlyRequiredProofs ? 1 : 0);
      hashcode = hashcode * 17 + (int)start;
      return hashcode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof LogRecord) {
         LogRecord other = (LogRecord)obj;
         return duration == other.getDuration() &&
                enableThreading == other.enableThreading &&
                kind == other.getKind() &&
                numberOfThreads == other.numberOfThreads &&
                onlyRequiredProofs == other.onlyRequiredProofs &&
                start == other.start;
      }
      else {
         return false;
      }
   }
}
