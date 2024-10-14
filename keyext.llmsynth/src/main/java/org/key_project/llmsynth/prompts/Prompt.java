package org.key_project.llmsynth.prompts;

import com.fasterxml.jackson.annotation.JsonIgnore;

public class Prompt implements Cloneable {
    public String input;
    public String output;
    public PromptType type;

    public boolean isAnswered;
    public long tokenUsage;

    public Prompt() {
        this(null, null, null, false);
    }

    public Prompt(PromptType type, String input) {
        this(type, input, null, false);
    }

    public Prompt(PromptType type, String input, String output, boolean isAnswered) {
        this.type = type;
        this.input = input;
        this.output = output;
        this.isAnswered = isAnswered;
    }

    @JsonIgnore
    public boolean isAnswered() {
        return this.isAnswered;
    }

    @JsonIgnore
    public Prompt clone() {
        return new Prompt(type, input, output, isAnswered);
    }

    @JsonIgnore
    public PromptMessage getInputMessage() {
        return new PromptMessage(type, input);
    }

    public PromptMessage getOutputMessage() {
        return new PromptMessage(PromptType.ASSISTANT, output);
    }
}