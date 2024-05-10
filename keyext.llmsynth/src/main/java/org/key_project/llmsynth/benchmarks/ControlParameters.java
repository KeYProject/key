package org.key_project.llmsynth.benchmarks;

public class ControlParameters {
    public int maxSearchDepth = Integer.MAX_VALUE;
    public long maxSearchWidth = Long.MAX_VALUE;
    public int maxRestarts = 1;
    public int keyTimeoutSeconds = 100;


    public ControlParameters setMaxSeachDepth(int value) {
        maxSearchDepth = value;
        return this;
    }

    public ControlParameters setMaxSearchWidth(long value) {
        maxSearchWidth = value;
        return this;
    }

    public ControlParameters setMaxRestarts(int value) {
        maxRestarts = value;
        return this;
    }

    public ControlParameters setKeyTimeoutSeconds(int keyTimeoutSeconds) {
        this.keyTimeoutSeconds = keyTimeoutSeconds;
        return this;
    }
}
