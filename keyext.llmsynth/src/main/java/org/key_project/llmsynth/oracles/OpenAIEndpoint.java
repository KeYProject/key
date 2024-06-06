package org.key_project.llmsynth.oracles;

import com.theokanning.openai.completion.chat.ChatCompletionChunk;
import com.theokanning.openai.completion.chat.ChatCompletionRequest;
import com.theokanning.openai.completion.chat.ChatMessage;
import com.theokanning.openai.completion.chat.ChatMessageRole;
import com.theokanning.openai.service.OpenAiService;
import io.reactivex.Flowable;
import org.key_project.llmsynth.prompts.Prompt;
import org.key_project.llmsynth.prompts.PromptAnswer;
import org.key_project.llmsynth.prompts.PromptMessage;
import org.key_project.llmsynth.prompts.PromptType;

import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

public class OpenAIEndpoint implements OracleEndpoint {
    public static final String MODEL_3_5_TURBO = "gpt-3.5-turbo";

    OpenAiService service;
    String gpt_model;
    HashMap<PromptAnswer, ChatMessage> buf_ans = new HashMap<>();
    HashMap<Prompt, ChatMessage> buf_pmp = new HashMap<>();

    public OpenAIEndpoint(OpenAiService service, String gpt_model) {
        this.service = service;
        this.gpt_model = gpt_model;
    }

    public OpenAIEndpoint(String  token, String gpt_model) {
        this(new OpenAiService(token), gpt_model);
    }


    public static OpenAIEndpoint forGpt_3_5_Turbo(String token) {
        return new OpenAIEndpoint(new OpenAiService(token), MODEL_3_5_TURBO);
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

        // todo: put this in dedicated class?
        return new PromptMessage() {
            @Override
            public String getContent() {
                return answer.getContent();
            }

            @Override
            public PromptType getMessageType() {
                return PromptType.ASSISTANT;
            }
        };
    }

    private String mkRole(PromptType promptType) {
        switch (promptType) {
            case USER: return ChatMessageRole.USER.value();
            case SYSTEM: return ChatMessageRole.SYSTEM.value();
            case ASSISTANT: return ChatMessageRole.ASSISTANT.value();
            default: throw new RuntimeException("Unknown prompt type");
        }
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
