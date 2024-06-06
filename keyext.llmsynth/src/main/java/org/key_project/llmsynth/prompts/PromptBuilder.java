package org.key_project.llmsynth.prompts;

import org.key_project.llmsynth.ClassInfo;
import org.key_project.llmsynth.LineSpan;
import org.key_project.llmsynth.MethodInfo;
import org.key_project.llmsynth.prompts.reasons.DirectPrompt;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

public class PromptBuilder
{
    final String DEFAULT_DELIM = "======================================================";

    List<PromptElement> elements = new ArrayList<>();
    boolean alreadyBuilt = false;
    String delimiter = DEFAULT_DELIM;
    Function<PromptAnswer, PromptResult> verificator;
    PromptType promptType = PromptType.USER;
    boolean removeHistory = false;

    public void setDelimiter(String delim) {
        delimiter = delim;
    }

    public PromptBuilder setVerificator(Function<PromptAnswer, PromptResult> verificator) {
        this.verificator = verificator;
        return this;
    }

    public PromptBuilder skipVerification() {
        setVerificator(PromptBuilder::autoReject);
        return this;
    }

    public PromptBuilder clone() {
        PromptBuilder the_clone;
        try {
            the_clone = (PromptBuilder) super.clone();
        } catch (CloneNotSupportedException e) {
            the_clone = new PromptBuilder();
        }

        the_clone.elements = List.copyOf(elements);
        the_clone.alreadyBuilt = false;
        the_clone.delimiter = this.delimiter;
        the_clone.verificator = this.verificator;
        the_clone.promptType = this.promptType;
        return the_clone;
    }

    //region printing
    public PromptBuilder textln(String text) {
        elements.add(writer -> writer.println(text));
        return this;
    }

    public PromptBuilder newln() {
        elements.add(PrintWriter::println);
        return this;
    }

    public PromptBuilder text(String text) {
        elements.add(writer -> writer.print(text));
        return this;
    }

    public PromptBuilder classTextInQuotes(ClassInfo classInfo) {
        textln("'''");
        for(var line : classInfo.getClassLines()) {
            textln(line);
        }
        textln("'''");
        return this;
    }

    public PromptBuilder methodBodyAndSignature(MethodInfo methodInfo) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public PromptBuilder methodBody(MethodInfo methodInfo) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public PromptBuilder methodSignature(MethodInfo methodInfo) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public PromptBuilder methodBodySlice(MethodInfo methodInfo, int begin, int end) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public PromptBuilder methodBodySlice(MethodInfo methodInfo, LineSpan pair) {
        throw new UnsupportedOperationException("Not implemented");
    }

    public PromptBuilder delimiter() {
        newln();
        elements.add(writer -> writer.println(this.delimiter));
        newln();
        return this;
    }

    public PromptBuilder generic(Consumer<PrintWriter> pe) {
        elements.add(pe::accept);
        return this;
    }
    //endregion

    public PromptBuilder asUserPrompt() {
        this.promptType = PromptType.USER;
        return this;
    }

    public PromptBuilder asAssistantPrompt() {
        this.promptType = PromptType.ASSISTANT;
        return this;
    }

    public PromptBuilder asSystemPrompt() {
        this.promptType = PromptType.SYSTEM;
        return this;
    }

    public PromptBuilder withoutHistory() {
        removeHistory = true;
        return this;
    }

    public Prompt build() {
        if (alreadyBuilt) throw new IllegalStateException("The prompt builder can only be used once");
        alreadyBuilt = true;
        return new Prompt(elements, verificator, promptType, removeHistory);
        // TODO: make a list chain, so that this can be immutable, too
    }

    public AnsweredPrompt answerWith(String answer) {
        return new AnsweredPrompt(build(), answer);
    }

    private static PromptResult autoReject(PromptAnswer a) {
        return PromptResult.reject(a, new DirectPrompt());
    }
}
