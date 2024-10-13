package org.key_project.llmsynth.benchmarks;

/**
 * A list of available LLMs to test
 */
public enum LLMChoice {
    /**
     * A human
     */
    HUMAN,
    /**
     * The program created an answer to a prompt
     */
    PROGRAM,
    GPT_3,
    GPT_4,
    GPT_4O,
    GPT_4O_MINI
}
