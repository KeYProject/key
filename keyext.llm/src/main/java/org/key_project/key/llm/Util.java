/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.io.IOException;
import java.util.Map;

import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;
import org.apache.hc.client5.http.classic.methods.HttpGet;
import org.apache.hc.client5.http.classic.methods.HttpPost;
import org.apache.hc.client5.http.impl.classic.HttpClients;
import org.apache.hc.core5.http.io.entity.StringEntity;

/**
 * Small HTTP helpers used by the settings UI (e.g. fetching the available models).
 *
 * @author Alexander Weigl
 */
public final class Util {
    private Util() {
    }

    public static Object post(String url, String authToken, Map<String, Object> data) {
        var request = new HttpPost(url);
        request.addHeader("Authorization", "Bearer " + authToken);
        request.addHeader("Content-Type", "application/json");
        request.addHeader("Accept", "application/json");
        var gson = new GsonBuilder().create();
        var stringBody = gson.toJson(data);
        request.setEntity(new StringEntity(stringBody));

        try (var client = HttpClients.createDefault()) {
            return client.execute(request, new DefaultChatCompletionsClient.ResponseHandler());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public static JsonObject httpGet(String url, String authToken) {
        var request = new HttpGet(url);
        request.addHeader("Authorization", "Bearer " + authToken);
        request.addHeader("Content-Type", "application/json");
        request.addHeader("Accept", "application/json");
        try (var client = HttpClients.createDefault()) {
            return client.execute(request,
                new DefaultChatCompletionsClient.ResponseHandlerObj());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
