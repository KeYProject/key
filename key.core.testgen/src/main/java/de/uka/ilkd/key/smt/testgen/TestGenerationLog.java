package de.uka.ilkd.key.smt.testgen;

public interface TestGenerationLog {
    void writeln(String string);

    void write(String string);

    void writeException(Throwable t);

    void testGenerationCompleted();
}
