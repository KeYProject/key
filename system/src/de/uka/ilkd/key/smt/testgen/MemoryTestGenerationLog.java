package de.uka.ilkd.key.smt.testgen;

/**
 * Implementation of {@link TestGenerationLog} which stores the log in memory.
 * @author Martin Hentschel
 */
public class MemoryTestGenerationLog implements TestGenerationLog {
   /**
    * The {@link StringBuffer} which stores all the content.
    */
   private final StringBuffer sb = new StringBuffer();

   /**
    * {@inheritDoc}
    */
   @Override
   public void writeln(String string) {
      sb.append(string);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void write(String string) {
      sb.append(string);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void writeException(Throwable t) {
      sb.append(t.getMessage());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void testGenerationCompleted() {
      sb.append("Test Generation Completed.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return sb.toString();
   }
}
