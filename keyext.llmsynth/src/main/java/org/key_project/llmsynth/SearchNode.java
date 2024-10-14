package org.key_project.llmsynth;

import com.fasterxml.jackson.annotation.*;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.*;

import java.util.*;
import java.util.function.Function;

public class SearchNode<T> implements ISearchNode, Cloneable {
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public Prompt prompt;
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public PromptStatus status;
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public PromptReason reason;


    @JsonBackReference
    public SearchNode<T> parent;
    private int depth;
    @JsonManagedReference
    public List<SearchNode<T>> reactions = new ArrayList<>();


    @JsonInclude(JsonInclude.Include.CUSTOM) // todo: only when false
    public boolean keepHistory = true;
    @JsonIgnore
    public Function<Prompt, VerificationResult> verificator;
    @JsonIgnore
    public T userData; // todo: when user allows it

    public SearchNode() {
        this(new Prompt(PromptType.USER, ""), PromptStatus.UNKNOWN, null);
    }

    public SearchNode(PromptReason reason_of_rejection) {
        this(null, PromptStatus.REJECTED, reason_of_rejection);
    }

    public SearchNode(Prompt prompt, PromptStatus status, PromptReason reason_of_rejection) {
        this(prompt, status, reason_of_rejection, null, new ArrayList<>(), true, null, null, 0);
    }

    public SearchNode(Prompt prompt, PromptStatus status, PromptReason reason, SearchNode<T> parent, List<SearchNode<T>> reactions, boolean keepHistory, Function<Prompt, VerificationResult> verificator, T userData, int depth) {
        this.prompt = prompt;
        this.status = status;
        this.reason = reason;
        setParent(parent);
        this.reactions = reactions;
        this.keepHistory = keepHistory;
        this.verificator = verificator;
        this.userData = userData;
        this.depth = depth;
    }

    private void addReaction(SearchNode<T> reaction) {
        reactions.add(reaction);
    }


    @Override
    public SearchNode<T> clone() {
        return new SearchNode<>(this.prompt.clone(), this.status, this.reason, this.parent, this.reactions, this.keepHistory, this.verificator, this.userData, this.depth);
    }

    @Override
    public ISearchNode getParent() {
        return parent;
    }

    public void setParent(SearchNode<T> parent) {
        this.parent = parent;
        this.depth = parent == null ? 0 : parent.depth+1;
    }

    @Override
    public PromptReason getReason() {
        return reason;
    }

    @Override
    public Prompt getPrompt() {
        return prompt;
    }

    @Override
    public boolean useForHistory() {
        return keepHistory;
    }

    public int getDepth() {
        return depth;
    }

    public void setResult(VerificationResult result) {
        assert result.getPrompt() == this.prompt;
        this.status = result.getStatus();
        this.reason = result.getReason();
    }

    public void setZeroDepth() {
        this.depth = parent == null ? 0 : parent.depth;
    }
}
