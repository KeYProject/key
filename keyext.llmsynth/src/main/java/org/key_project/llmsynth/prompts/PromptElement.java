package org.key_project.llmsynth.prompts;

import java.io.PrintWriter;

@FunctionalInterface
public interface PromptElement {
    void print(PrintWriter printWriter);
}
