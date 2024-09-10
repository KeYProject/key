package org.key_project.llmsynth.oracles;

import com.theokanning.openai.completion.chat.ChatCompletionChunk;
import com.theokanning.openai.completion.chat.ChatCompletionRequest;
import com.theokanning.openai.completion.chat.ChatMessage;
import com.theokanning.openai.completion.chat.ChatMessageRole;
import com.theokanning.openai.service.OpenAiService;
import io.reactivex.Flowable;
import org.key_project.llmsynth.prompts.PromptMessage;
import org.key_project.llmsynth.prompts.PromptType;

import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * The OracleEndpoint implementation for OpenAI
 */
public class OpenAIEndpoint implements OracleEndpoint {
    public static final String MODEL_3_5_TURBO = "gpt-3.5-turbo";

    OpenAiService service;
    String gpt_model;
    String token = null;

    public OpenAIEndpoint(OpenAiService service, String gpt_model) {
        this.service = service;
        this.gpt_model = gpt_model;
    }

    public OpenAIEndpoint(String token, String gpt_model) {
        this(new OpenAiService(token), gpt_model);
        this.token = token;
    }


    public static OpenAIEndpoint forGpt_3_5_Turbo(String token) {
        return new OpenAIEndpoint(token, MODEL_3_5_TURBO);
    }

    public void shutdown() {
        service.shutdownExecutor();
    }

    public void resetConnection() {
        this.shutdown();
        if (token == null) throw new UnsupportedOperationException("No token was probided during construction to reestablish a connection with");
        this.service = new OpenAiService(this.token);
    }

    @Override
    public PromptMessage ask(List<PromptMessage> prompts) {
        var messages = prompts.stream().map(this::convert).collect(Collectors.toList());
        ChatCompletionRequest ccr = createCompletionRequest(messages);

        Flowable<ChatCompletionChunk> flowable = service.streamChatCompletion(ccr);

        ChatMessage answer = service
                .mapStreamToAccumulator(flowable)
                .lastElement()
                .blockingGet()
                .getAccumulatedMessage();

        return new PromptMessage(PromptType.ASSISTANT, answer.getContent());
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

    private ChatCompletionRequest createCompletionRequest(List<ChatMessage> messages) {
        return ChatCompletionRequest
                .builder()
                .model(gpt_model)
                .messages(messages)
                .n(1)
                .maxTokens(2048)
                .logitBias(new HashMap<>())
                .build();
    }
}
