package org.key_project.llmsynth.oracles;

import com.theokanning.openai.completion.chat.*;
import com.theokanning.openai.service.OpenAiService;
import io.reactivex.Flowable;
import org.key_project.llmsynth.ISearchNode;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptMessage;
import org.key_project.llmsynth.prompts.PromptType;

import java.util.*;

public class OracleGpt3_5_Turbo {
    public static boolean print_Messages = false;
    OpenAiService service;

    private final String token;

    private final ChatMessage systemMessage = new ChatMessage(ChatMessageRole.SYSTEM.value(), "");

    public OracleGpt3_5_Turbo(String token) {
        service = new OpenAiService(token);
        this.token = token;
    }

    // Finalize
    public void shutdown() {
        service.shutdownExecutor();
    }

    public void resetConnection() {
        this.shutdown();
        this.service = new OpenAiService(this.token);
    }

    public void answerPromptOnNode(ISearchNode node) {
        Prompt prompt = node.getPrompt();
        if (prompt.isAnswered()) throw new IllegalArgumentException("The prompt is already answered");

        PromptMessage question = node.getPrompt().getInputMessage();
        List<PromptMessage> messages = new ArrayList<>();

        ISearchNode current = node;
        while (current.useForHistory()) {
            current = current.getParent();
            if (current == null) break;
            if (current.getPrompt() == null) continue;
            messages.add(current.getPrompt().getOutputMessage());
            messages.add(current.getPrompt().getInputMessage());
        }
        Collections.reverse(messages);
        messages.add(prompt.getInputMessage());


        int requestCount = 0;

        ChatMessage answer = null;
        do {
            try {
                ChatCompletionRequest ccr = createCompletionRequest(messages);

                Flowable<ChatCompletionChunk> flowable = service.streamChatCompletion(ccr);

                answer = service
                        .mapStreamToAccumulator(flowable)
                        .lastElement()
                        .blockingGet()
                        .getAccumulatedMessage();
            } catch (RuntimeException e) {
                System.err.println("Error prompting GPT, resetting connection: " + e.getMessage());
                this.resetConnection();
            }
        } while (answer == null && requestCount++ < 3);

        prompt.output = answer.getContent();

        /*if (print_Messages) {
            System.err.println("=============================================================");
            System.err.println(prompt.input);
            System.err.println("-------------------------------------------------------------");
            System.err.println(prompt.output);
        }*/
    }


    private ChatMessage fromInput(Prompt node) {
        var text = node.toString();
        return new ChatMessage(ChatMessageRole.USER.value(), text);
    }

    private ChatMessage fromOutput(Prompt node) {
        var text = node.toString();
        return new ChatMessage(ChatMessageRole.USER.value(), text);
    }

    private ChatCompletionRequest createCompletionRequest(List<PromptMessage> messages) {
        List<ChatMessage> chats = messages.stream().map(this::convert).toList();
        return ChatCompletionRequest
                .builder()
                .model("gpt-3.5-turbo-0125")
                //.model("gpt-4o")
                .messages(chats)
                .n(1)
                .maxTokens(512)
                .logitBias(new HashMap<>())
                .build();
    }

    private String mkRole(PromptType promptType) {
        return switch (promptType) {
            case USER -> ChatMessageRole.USER.value();
            case SYSTEM -> ChatMessageRole.SYSTEM.value();
            case ASSISTANT -> ChatMessageRole.ASSISTANT.value();
            default -> throw new RuntimeException("Unknown prompt type");
        };
    }

    private ChatMessage convert(PromptMessage message) {
        var typ = mkRole(message.getMessageType());
        return new ChatMessage(typ, message.getContent());
    }
}
