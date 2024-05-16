package org.key_project.llmsynth;

public class Nothing {
    private static Nothing instance = new Nothing();
    public static Nothing getInstance() {
        return instance;
    }
    private Nothing() {}

}
