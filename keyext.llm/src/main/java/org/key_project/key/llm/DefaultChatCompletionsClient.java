/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Map;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import org.apache.hc.client5.http.classic.methods.HttpPost;
import org.apache.hc.client5.http.impl.classic.AbstractHttpClientResponseHandler;
import org.apache.hc.client5.http.impl.classic.HttpClients;
import org.apache.hc.core5.http.HttpEntity;
import org.apache.hc.core5.http.ParseException;
import org.apache.hc.core5.http.io.entity.EntityUtils;
import org.apache.hc.core5.http.io.entity.StringEntity;

/**
 * Default {@link ChatCompletionsClient} implementation based on Apache HttpClient 5, speaking the
 * OpenAI-compatible chat-completions protocol.
 *
 * @author Alexander Weigl
 */
public class DefaultChatCompletionsClient implements ChatCompletionsClient {

    /** Suffix appended to the endpoint configured in the {@link LlmSession}. */
    public static final String COMPLETIONS_PATH = "/openai/chat/completions";

    @Override
    public Map<String, Object> complete(LlmSession session, AgentRequest request) throws Exception {
        var url = session.getApiEndpoint() + COMPLETIONS_PATH;
        var http = new HttpPost(url);
        http.addHeader("Authorization", "Bearer " + session.getAuthToken());
        http.addHeader("Content-Type", "application/json");
        http.addHeader("Accept", "application/json");

        var payload = new LinkedHashMap<String, Object>();
        payload.put("model", request.model());
        payload.put("messages", request.messages());
        if (request.tools() != null && !request.tools().isEmpty()) {
            payload.put("tools", request.tools());
            payload.put("tool_choice", "auto");
        }
        if (request.temperature() != null) {
            payload.put("temperature", request.temperature());
        }
        if (request.maxOutputTokens() != null) {
            payload.put("max_tokens", request.maxOutputTokens());
        }

        var gson = new GsonBuilder().create();
        http.setEntity(new StringEntity(gson.toJson(payload)));

        try (var client = HttpClients.createDefault()) {
            return client.execute(http, new ResponseHandler());
        }
    }

    public static class ResponseHandler
            extends AbstractHttpClientResponseHandler<Map<String, Object>> {
        @Override
        public Map<String, Object> handleEntity(HttpEntity entity) throws IOException {
            String content;
            try {
                content = EntityUtils.toString(entity);
            } catch (ParseException e) {
                throw new RuntimeException(e);
            }
            try {
                return new GsonBuilder().create().fromJson(content, Map.class);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

    public static class ResponseHandlerObj extends AbstractHttpClientResponseHandler<JsonObject> {
        @Override
        public JsonObject handleEntity(HttpEntity entity) throws IOException {
            String content;
            try {
                content = EntityUtils.toString(entity);
            } catch (ParseException e) {
                throw new RuntimeException(e);
            }
            try {
                return new GsonBuilder().create().fromJson(content, JsonObject.class);
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }
}
