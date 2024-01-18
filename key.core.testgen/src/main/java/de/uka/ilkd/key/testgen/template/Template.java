package de.uka.ilkd.key.testgen.template;

public interface Template {
    String shCompileWithOpenJML();

    String shCompileWithOpenJML(String openJMLPath, String objenesisPath);

    String shExecuteWithOpenJML(String path, String objenesisPath);
}
