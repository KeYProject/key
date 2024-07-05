package org.key_project.llmsynth;

/**
 * A singleton class that represents nothing.
 * Used to show unused type parameters.
 */
public class Nothing {
    private static Nothing instance = new Nothing();
    public static Nothing getInstance() {
        return instance;
    }
    private Nothing() {}

}
