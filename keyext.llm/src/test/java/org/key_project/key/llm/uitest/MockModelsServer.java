/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.uitest;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.nio.charset.StandardCharsets;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpServer;

/**
 * A mock OpenAI-compatible API server for UI tests: it serves a canned model list under
 * {@code /openai/models} so that the "Fetch Models" button of the LLM settings panel is driven by
 * deterministic remote data.
 */
public final class MockModelsServer implements AutoCloseable {

    /** The ids the mock endpoint reports. */
    public static final String[] MOCK_MODELS =
        { "mock-model-1", "mock-model-2", "mock-model-3" };

    private final HttpServer server;

    public MockModelsServer() throws IOException {
        server = HttpServer.create(new InetSocketAddress("127.0.0.1", 0), 0);
        server.createContext("/", this::handle);
        server.start();
    }

    /** The base URL clients should dial, e.g. {@code http://127.0.0.1:4711}. */
    public String getBaseUrl() {
        return "http://127.0.0.1:" + server.getAddress().getPort();
    }

    private void handle(HttpExchange exchange) throws IOException {
        byte[] body;
        int status;
        if ("/openai/models".equals(exchange.getRequestURI().getPath())) {
            StringBuilder json = new StringBuilder("{\"data\":[");
            for (int i = 0; i < MOCK_MODELS.length; i++) {
                if (i > 0) {
                    json.append(',');
                }
                json.append("{\"id\":\"").append(MOCK_MODELS[i]).append("\"}");
            }
            json.append("]}");
            body = json.toString().getBytes(StandardCharsets.UTF_8);
            status = 200;
        } else {
            body = "{}".getBytes(StandardCharsets.UTF_8);
            status = 404;
        }
        exchange.getResponseHeaders().add("Content-Type", "application/json");
        exchange.sendResponseHeaders(status, body.length);
        try (var os = exchange.getResponseBody()) {
            os.write(body);
        }
    }

    @Override
    public void close() {
        server.stop(0);
    }
}
