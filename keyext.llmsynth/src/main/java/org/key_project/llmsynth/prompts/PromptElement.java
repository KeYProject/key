package org.key_project.llmsynth.prompts;

import java.io.PrintWriter;

/**
 * Part of a prompt. Used to avoid early stringifycation
 */
@FunctionalInterface
public interface PromptElement {
    void print(PrintWriter printWriter);
}
