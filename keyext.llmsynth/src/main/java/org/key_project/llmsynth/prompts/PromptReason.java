package org.key_project.llmsynth.prompts;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonInclude;
import org.key_project.llmsynth.ISearchNode;

/**
 * If a prompt strategy is invoked, it has a reason.
 * This encodes the reason via subclasses, but also allows access to previous prompts in the conversation history.
 */
public class PromptReason {
    @JsonInclude
    public String description;
//    @JsonBackReference
    @JsonIgnore
    ISearchNode node = null;
//    @JsonManagedReference

    @JsonIgnore
    int depth = 0;

    public PromptReason(String description) {
        this.description = description;
    }

    public PromptReason(String description, ISearchNode node) {
        this(description);
        this.node = node;
        this.depth = node.getParent().getReason().depth + 1;
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
    public PromptReason getPreviousReason() {
        return node.getParent().getReason();
    }

    public void setNode(ISearchNode node) {
        assert this.node == null;
        this.node = node;
        this.depth = node.getParent().getReason().depth+1;
    }

    /**
     *
     * @return The prompt that failed to verify
     */
    @JsonIgnore
    public Prompt getPrompt() {
        return node.getPrompt();
    }

}
