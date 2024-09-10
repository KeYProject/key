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
    /**
     * OpenAI's GPT 3.5-Turbo
     */
    GPT_3_5_TURBO
}
