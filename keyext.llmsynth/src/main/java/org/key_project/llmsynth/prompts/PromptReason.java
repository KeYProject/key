package org.key_project.llmsynth.prompts;

/**
 * If a prompt strategy is invoked, it has a reason.
 * This encodes the reason via subclasses, but also allows access to previous prompts in the conversation history.
 */
public class PromptReason {
    PromptReason parent = null;

    // The prompt that was rejected
    PromptResult result = null;
    int depth = 0;

    public PromptReason() {
    }

    public PromptReason(PromptReason parent) {
        this.parent = parent;
        this.depth = parent.depth + 1;
    }

    /**
     *
     * @return The length of history
     */
    public int getDepth() {
        return depth;
    }

    /**
     *
     * @return The previous prompt (and why it failed)
     */
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
    public Prompt getPrompt() {
        return result.getPrompt();
    }

    /**
     *
     * @return The answer to the prompt that failed to verify
     */
    public PromptAnswer getAnswer() {
        return result.getAnswer();
    }
}
