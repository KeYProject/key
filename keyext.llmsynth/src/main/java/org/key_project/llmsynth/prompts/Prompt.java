package org.key_project.llmsynth.prompts;

import com.fasterxml.jackson.annotation.JsonIgnore;

public class Prompt implements Cloneable {
    public String input;
    public String output;
    public PromptType type;

    public Prompt() {
        this(null, null, null);
    }

    public Prompt(PromptType type, String input) {
        this(type, input, null);
    }

    public Prompt(PromptType type, String input, String output) {
        this.type = type;
        this.input = input;
        this.output = output;
    }

    @JsonIgnore
    public boolean isAnswered() {
        return output != null;
    }

    @JsonIgnore
    public Prompt clone() {
        return new Prompt(type, input, output);
    }

    @JsonIgnore
    public PromptMessage getInputMessage() {
        return new PromptMessage(type, input);
    }

    public PromptMessage getOutputMessage() {
        return new PromptMessage(PromptType.ASSISTANT, output);
    }
}