package org.key_project.llmsynth.prompts;

import com.fasterxml.jackson.annotation.JsonBackReference;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonManagedReference;

import java.util.ArrayList;
import java.util.List;

/**
 * If a prompt strategy is invoked, it has a reason.
 * This encodes the reason via subclasses, but also allows access to previous prompts in the conversation history.
 */
public class PromptReason {
    @JsonInclude
    public String description;
//    @JsonBackReference
    @JsonIgnore
    PromptReason parent = null;
//    @JsonManagedReference
    @JsonIgnore
    List<PromptResult> reactions = new ArrayList<>();

//    @JsonManagedReference
    @JsonIgnore
    PromptResult result = null; // The prompt that was rejected
    @JsonIgnore
    int depth = 0;

    public PromptReason(String description) {
        this.description = description;
    }

    public PromptReason(String description, PromptReason parent) {
        this(description);
        this.parent = parent;
        this.depth = parent.depth + 1;
    }

    /**
     *
     * @return The length of history
     */
    @JsonIgnore
    public int getDepth() {
        return depth;
    }

    /**
     *
     * @return The previous prompt (and why it failed)
     */
    @JsonIgnore
    public PromptReason getParent() {
        return parent;
    }

    public void setParent(PromptReason parent) {
        assert this.parent == null;
        this.parent = parent;
        this.depth = parent.depth+1;
    }

    public void setResult(PromptResult r) {
        assert r.getReason() == this;
        this.result = r;
    }

    /**
     *
     * @return The prompt that failed to verify
     */
    @JsonIgnore
    public Prompt getPrompt() {
        return result.getPrompt();
    }

    /**
     *
     * @return The answer to the prompt that failed to verify
     */
    @JsonIgnore
    public PromptAnswer getAnswer() {
        return result.getAnswer();
    }

    public void addReaction(PromptResult result) {
        reactions.add(result);
    }

    @JsonIgnore
    public List<PromptResult> getReactions() {
        return reactions;
    }
}
