package org.key_project.llmsynth;


import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

public class ClassInfo {
    private String className;
    private List<String> classLines;

    public ClassInfo(String className, Path classFile) throws IOException {
        this.className = className;
        this.classLines = Files.readAllLines(classFile);
    }

    public List<String> getClassLines() {
        return classLines;
    }
}
