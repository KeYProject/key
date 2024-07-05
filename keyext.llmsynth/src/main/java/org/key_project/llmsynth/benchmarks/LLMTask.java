package org.key_project.llmsynth.benchmarks;

import org.key_project.llmsynth.LLMTaskTag;

/**
 * The base class for possible tasks.
 * Mainly used for tagging the classfor easier exhaustive matching.
 */
public class LLMTask {
    public final LLMTaskTag tag;

    public LLMTask(LLMTaskTag tag) {
        this.tag = tag;
    }
}
