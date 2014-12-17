package de.uka.ilkd.key.smt.testgen;

public interface TestGenerationLog {
   public void writeln(String string);

   public void write(String string);
   
   public void writeException(Throwable t);
   
   public void testGenerationCompleted();
}
