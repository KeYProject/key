package org.key_project.llmsynth.benchmarks;

/**
 * All the parameters that can change the behaviour of the BenchmarkRunner running the benchmark
 */
public class ControlParameters {
    /**
     * The maximum depth of the search tree.
     * I.e.: How many verification failures to accept in a conversation.
     */
    public int maxSearchDepth = Integer.MAX_VALUE;

    /**
     * The maximum width of the search tree.
     * I.e.: How many alternative continuations of a conversation are allowed.
     */
    public long maxSearchWidth = Long.MAX_VALUE;

    /**
     * How often a conversation is started in order to find a solution.
     */
    public int maxRestarts = 1;

    /**
     * The maximum amount of time to wait for key verification.
     * TODO: this does not work properly at the moment
     */
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
