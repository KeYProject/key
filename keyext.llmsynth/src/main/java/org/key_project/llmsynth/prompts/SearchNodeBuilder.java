package org.key_project.llmsynth.prompts;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.LineSpan;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.SearchNode;
import org.key_project.llmsynth.prompts.reasons.DirectPrompt;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * A utility class for creating search nodes
 */
public class SearchNodeBuilder<T>
{
    final String DEFAULT_DELIM = "======================================================";

    List<PromptElement> elements = new ArrayList<>();
    String delimiter = DEFAULT_DELIM;

    SearchNode<T> referenceNode;
    SearchNode<T> parent;

    public SearchNodeBuilder(SearchNode<T> parent) {
        this.parent = parent;
        reset();
    }

    public void setDelimiter(String delim) {
        this.delimiter = delim;
    }

    public SearchNodeBuilder<T> setVerificator(Function<Prompt, VerificationResult> verificator) {
        this.referenceNode.verificator = verificator;
        return this;
    }

    public SearchNodeBuilder<T> skipVerification() {
        setVerificator(SearchNodeBuilder::autoReject);
        return this;
    }

    public void reset() {
        this.referenceNode = new SearchNode<>();
        this.referenceNode.setParent(parent);
        this.delimiter = DEFAULT_DELIM;
        this.elements.clear();
    }

    //region printing
    public SearchNodeBuilder<T> textln(String text) {
        elements.add(writer -> writer.println(text));
        return this;
    }

    public SearchNodeBuilder<T> newln() {
        elements.add(PrintWriter::println);
        return this;
    }

    public SearchNodeBuilder<T> text(String text) {
        elements.add(writer -> writer.print(text));
        return this;
    }

    public SearchNodeBuilder<T> classTextInQuotes(ClassInfo classInfo) {
        textln("'''");
        for(var line : classInfo.getClassLines()) {
            textln(line);
        }
        textln("'''");
        return this;
    }

    public SearchNodeBuilder<T> methodBodyAndSignature(MethodInfo methodInfo) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public SearchNodeBuilder<T> methodBody(MethodInfo methodInfo) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public SearchNodeBuilder<T> methodSignature(MethodInfo methodInfo) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public SearchNodeBuilder<T> methodBodySlice(MethodInfo methodInfo, int begin, int end) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public SearchNodeBuilder<T> methodBodySlice(MethodInfo methodInfo, LineSpan pair) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public SearchNodeBuilder<T> delimiter() {
        newln();
        elements.add(writer -> writer.println(this.delimiter));
        newln();
        return this;
    }

    public SearchNodeBuilder<T> generic(Consumer<PrintWriter> pe) {
        elements.add(pe::accept);
        return this;
    }
    //endregion

    public SearchNodeBuilder<T> asUserPrompt() {
        this.referenceNode.prompt.type = PromptType.USER;
        return this;
    }

    public SearchNodeBuilder<T> asAssistantPrompt() {
        this.referenceNode.prompt.type = PromptType.ASSISTANT;
        return this;
    }

    public SearchNodeBuilder<T> asSystemPrompt() {
        this.referenceNode.prompt.type = PromptType.SYSTEM;
        return this;
    }

    public SearchNodeBuilder<T> withoutHistory() {
        this.referenceNode.keepHistory = false;
        return this;
    }

    private String stringifyElements() {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);;
        elements.forEach(e -> e.print(pw));
        return sw.toString();
    }

    public SearchNode<T> build() {
        this.referenceNode.prompt.input = stringifyElements();
        return this.referenceNode.clone();
    }

    public Iterable<SearchNode<T>> buildIterable() {
        return List.of(build());
    }

    public SearchNodeBuilder<T> answerWith(String answer) {
        this.referenceNode.prompt.output = answer;
        return this;
    }

    public SearchNodeBuilder<T> isAnswered() {
        this.referenceNode.prompt.isAnswered = true;
        return this;
    }

    private static VerificationResult autoReject(Prompt a) {
        return VerificationResult.reject(a, new DirectPrompt());
    }
}
