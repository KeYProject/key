/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.mcp.server;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URLDecoder;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import io.modelcontextprotocol.json.McpJsonMapper;
import io.modelcontextprotocol.json.TypeRef;
import io.modelcontextprotocol.spec.McpError;
import io.modelcontextprotocol.spec.McpSchema;
import io.modelcontextprotocol.spec.McpServerSession;
import io.modelcontextprotocol.spec.McpServerTransport;
import io.modelcontextprotocol.spec.McpServerTransportProvider;
import io.modelcontextprotocol.spec.ProtocolVersions;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import reactor.core.publisher.Flux;
import reactor.core.publisher.Mono;

/**
 * An MCP (Model Context Protocol) server transport that speaks the HTTP with Server-Sent Events
 * (SSE) transport specification on the JDK's {@link com.sun.net.httpserver.HttpServer}.
 * <p>
 * The transport manages the standard two endpoints:
 * <ul>
 * <li>{@code GET /sse} - establishes a long-lived SSE stream for server-to-client events. A new
 * MCP session is created per stream (via {@link McpServerSession.Factory}); the client is told
 * where to POST its requests through the {@code endpoint} event. The endpoint event carries the
 * root-relative path ({@code /messages?sessionId=…}) rather than an absolute URL: every
 * RFC&nbsp;3986 resolving client (including the SDK's {@code HttpClientSseClientTransport},
 * whose default validator explicitly allows relative endpoints) then targets the right origin
 * regardless of whether it was configured with the bare origin or with the full
 * {@code http://host:port/sse} URL.</li>
 * <li>{@code POST /messages} - receives client-to-server JSON-RPC messages for a session
 * (identified by the {@code sessionId} query parameter) and dispatches them through the SDK's
 * session handling. Responses travel back over the session's SSE stream.</li>
 * </ul>
 * <p>
 * All protocol state (version negotiation, JSON-RPC framing, tool dispatch) lives in the MCP SDK
 * ({@code McpServer}); this class only provides the HTTP + SSE plumbing and per-session
 * transports. The class is deliberately modelled after the SDK's own
 * {@code HttpServletSseServerTransportProvider}, the only difference being that it serves the
 * endpoints on {@code com.sun.net.httpserver} instead of a servlet container, so no servlet
 * container is required.
 * <p>
 * A static bearer token can be configured: every request must then carry
 * {@code Authorization: Bearer <token>}.
 *
 * @author Alexander Weigl
 */
public class SseHttpServerTransportProvider implements McpServerTransportProvider, HttpHandler {

    /** Path of the SSE stream endpoint. */
    public static final String SSE_ENDPOINT = "/sse";

    /** Path of the client-to-server message endpoint. */
    public static final String MESSAGE_ENDPOINT = "/messages";

    /** Query parameter carrying the session id on the message endpoint. */
    public static final String SESSION_ID = "sessionId";

    /** SSE event type for regular JSON-RPC messages. */
    public static final String MESSAGE_EVENT = "message";

    /** SSE event type announcing the message endpoint of a session. */
    public static final String ENDPOINT_EVENT = "endpoint";

    /** Maximum size in bytes of a single request body. */
    private static final int MAX_BODY_BYTES = 16 * 1024 * 1024;

    /** Interval between SSE keep-alive comment pings. */
    private static final long KEEP_ALIVE_MILLIS = 15_000;

    private static final Logger logger =
        LoggerFactory.getLogger(SseHttpServerTransportProvider.class);

    private final McpJsonMapper jsonMapper;

    private final @Nullable String token;

    /** Active MCP sessions, keyed by transport (SSE stream) session id. */
    private final Map<String, McpServerSession> sessions = new ConcurrentHashMap<>();

    private final AtomicBoolean closing = new AtomicBoolean(false);

    /** The session factory handed over by the {@code McpServer} during its build. */
    private volatile McpServerSession.Factory sessionFactory;

    /**
     * Creates the transport.
     *
     * @param jsonMapper the JSON mapper used to serialize/deserialize JSON-RPC messages
     * @param token optional static bearer token; {@code null} or blank to allow anonymous access
     */
    public SseHttpServerTransportProvider(McpJsonMapper jsonMapper, @Nullable String token) {
        this.jsonMapper = jsonMapper;
        this.token = token;
    }

    // ------------------------------------------------------------ McpServerTransportProvider

    @Override
    public void setSessionFactory(McpServerSession.Factory sessionFactory) {
        this.sessionFactory = sessionFactory;
    }

    @Override
    public List<String> protocolVersions() {
        return List.of(ProtocolVersions.MCP_2024_11_05);
    }

    @Override
    public Mono<Void> notifyClients(String method, Object params) {
        if (sessions.isEmpty()) {
            return Mono.empty();
        }
        return Flux.fromIterable(sessions.values())
                .flatMap(session -> session.sendNotification(method, params)
                        .doOnError(e -> logger.error("Failed to send message to session {}: {}",
                            session.getId(), e.getMessage()))
                        .onErrorComplete())
                .then();
    }

    @Override
    public Mono<Void> notifyClient(String sessionId, String method, Object params) {
        var session = sessions.get(sessionId);
        if (session == null) {
            logger.debug("Session {} not found", sessionId);
            return Mono.empty();
        }
        return session.sendNotification(method, params);
    }

    @Override
    public Mono<Void> closeGracefully() {
        closing.set(true);
        logger.debug("Closing MCP SSE transport with {} active sessions", sessions.size());
        return Flux.fromIterable(sessions.values()).flatMap(McpServerSession::closeGracefully)
                .then()
                .doOnSuccess(v -> sessions.clear());
    }

    // ------------------------------------------------------------ HttpHandler

    @Override
    public void handle(HttpExchange exchange) throws IOException {
        if (closing.get()) {
            exchange.sendResponseHeaders(HttpURLConnection.HTTP_UNAVAILABLE, -1);
            exchange.close();
            return;
        }
        if (!checkToken(exchange)) {
            return;
        }
        String method = exchange.getRequestMethod();
        String path = exchange.getRequestURI().getPath();
        switch (method) {
            case "GET" -> {
                if (SSE_ENDPOINT.equals(path)) {
                    handleSse(exchange);
                } else {
                    notFound(exchange);
                }
            }
            case "POST" -> {
                if (MESSAGE_ENDPOINT.equals(path)) {
                    handleMessage(exchange);
                } else {
                    notFound(exchange);
                }
            }
            default -> exchange.sendResponseHeaders(HttpURLConnection.HTTP_BAD_METHOD, -1);
        }
        if (!"GET".equals(method) && !"POST".equals(method)) {
            exchange.close();
        }
    }

    private void notFound(HttpExchange exchange) throws IOException {
        exchange.sendResponseHeaders(HttpURLConnection.HTTP_NOT_FOUND, -1);
        exchange.close();
    }

    /** Rejects the exchange unless it carries the configured bearer token. */
    private boolean checkToken(HttpExchange exchange) throws IOException {
        if (token == null || token.isBlank()) {
            return true;
        }
        String auth = exchange.getRequestHeaders().getFirst("Authorization");
        if (auth != null && auth.startsWith("Bearer ")
                && token.equals(auth.substring("Bearer ".length()))) {
            return true;
        }
        exchange.sendResponseHeaders(HttpURLConnection.HTTP_UNAUTHORIZED, -1);
        exchange.close();
        return false;
    }

    /** Serves the long-lived SSE stream of one MCP session. Blocks until the peer disconnects. */
    private void handleSse(HttpExchange exchange) throws IOException {
        var response = exchange.getResponseHeaders();
        response.set("Content-Type", "text/event-stream");
        response.set("Cache-Control", "no-cache");
        response.set("Connection", "keep-alive");
        exchange.sendResponseHeaders(HttpURLConnection.HTTP_OK, 0);

        OutputStream out = exchange.getResponseBody();
        String sessionId = UUID.randomUUID().toString();
        var transport = new SseSessionTransport(sessionId, out);
        var session = sessionFactory.create(transport);
        sessions.put(sessionId, session);
        logger.info("KeY MCP server: SSE session {} established", sessionId);
        try {
            sendEvent(out, ENDPOINT_EVENT, MESSAGE_ENDPOINT + "?" + SESSION_ID + "=" + sessionId);
            // Keep the stream open; periodic comment pings detect a disconnected peer.
            while (!transport.closed) {
                Thread.sleep(KEEP_ALIVE_MILLIS);
                synchronized (transport.writeLock) {
                    if (transport.closed) {
                        break;
                    }
                    out.write((": ping\n\n").getBytes(StandardCharsets.UTF_8));
                    out.flush();
                }
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        } catch (IOException e) {
            logger.debug("KeY MCP server: SSE session {} closed by peer", sessionId);
        } finally {
            sessions.remove(sessionId);
            try {
                out.close();
            } catch (IOException ignored) {
                // already closed
            }
            exchange.close();
            logger.info("KeY MCP server: SSE session {} closed", sessionId);
        }
    }

    /** Receives one client-to-server JSON-RPC message and dispatches it to the session. */
    private void handleMessage(HttpExchange exchange) throws IOException {
        String sessionId = queryParam(exchange, SESSION_ID);
        if (sessionId == null) {
            sendJsonError(exchange, HttpURLConnection.HTTP_BAD_REQUEST,
                "Missing sessionId query parameter on the message endpoint");
            return;
        }
        McpServerSession session = sessions.get(sessionId);
        if (session == null) {
            sendJsonError(exchange, HttpURLConnection.HTTP_NOT_FOUND,
                "Unknown session: " + sessionId);
            return;
        }
        String body = readBody(exchange.getRequestBody(), MAX_BODY_BYTES);
        if (body == null) {
            sendJsonError(exchange, HttpURLConnection.HTTP_ENTITY_TOO_LARGE,
                "Request body exceeds the maximum size of " + MAX_BODY_BYTES + " bytes");
            return;
        }
        try {
            McpSchema.JSONRPCMessage message =
                McpSchema.deserializeJsonRpcMessage(jsonMapper, body);
            session.handle(message).block();
            exchange.sendResponseHeaders(HttpURLConnection.HTTP_OK, -1);
            exchange.close();
        } catch (Exception e) {
            logger.error("KeY MCP server: failed to process message for session {}: {}",
                sessionId, e.getMessage());
            sendJsonError(exchange, HttpURLConnection.HTTP_INTERNAL_ERROR,
                "Failed to process message: " + e.getMessage());
        }
    }

    private void sendJsonError(HttpExchange exchange, int status, String message)
            throws IOException {
        String json =
            jsonMapper.writeValueAsString(McpError.builder(McpSchema.ErrorCodes.INTERNAL_ERROR)
                    .message(message).build());
        byte[] body = json.getBytes(StandardCharsets.UTF_8);
        exchange.getResponseHeaders().set("Content-Type", "application/json");
        exchange.sendResponseHeaders(status, body.length);
        exchange.getResponseBody().write(body);
        exchange.close();
    }

    /** Reads the request body, bounded by {@code maxBytes}; returns {@code null} if too large. */
    private static @Nullable String readBody(InputStream in, int maxBytes) throws IOException {
        try (in) {
            byte[] buf = new byte[8192];
            var out = new java.io.ByteArrayOutputStream();
            long total = 0;
            int n;
            while ((n = in.read(buf)) >= 0) {
                total += n;
                if (total > maxBytes) {
                    return null;
                }
                out.write(buf, 0, n);
            }
            return out.toString(StandardCharsets.UTF_8);
        }
    }

    private static @Nullable String queryParam(HttpExchange exchange, String name) {
        String query = exchange.getRequestURI().getRawQuery();
        if (query == null) {
            return null;
        }
        for (String pair : query.split("&")) {
            int i = pair.indexOf('=');
            if (i < 0) {
                continue;
            }
            if (pair.substring(0, i).equals(name)) {
                return URLDecoder.decode(pair.substring(i + 1), StandardCharsets.UTF_8);
            }
        }
        return null;
    }

    private static void sendEvent(OutputStream out, String eventType, String data)
            throws IOException {
        out.write(("event: " + eventType + "\n").getBytes(StandardCharsets.UTF_8));
        out.write(("data: " + data + "\n\n").getBytes(StandardCharsets.UTF_8));
        out.flush();
    }

    /**
     * The per-session transport of one SSE stream: writes the SDK's outgoing JSON-RPC messages as
     * {@code message} SSE events and hands the JSON mapper to the session.
     */
    private final class SseSessionTransport implements McpServerTransport {
        private final String sessionId;
        private final OutputStream out;

        /** Serializes SSE writes (concurrent {@code sendMessage} calls and keep-alive pings). */
        private final Object writeLock = new Object();

        private volatile boolean closed;

        private SseSessionTransport(String sessionId, OutputStream out) {
            this.sessionId = sessionId;
            this.out = out;
        }

        @Override
        public Mono<Void> sendMessage(McpSchema.JSONRPCMessage message) {
            return Mono.fromRunnable(() -> {
                synchronized (writeLock) {
                    if (closed) {
                        return;
                    }
                    try {
                        sendEvent(out, MESSAGE_EVENT, jsonMapper.writeValueAsString(message));
                    } catch (Exception e) {
                        closed = true;
                        sessions.remove(sessionId);
                        logger.error("KeY MCP server: failed to send message to session {}: {}",
                            sessionId, e.getMessage());
                        throw new IllegalStateException("Failed to send SSE message", e);
                    }
                }
            });
        }

        @Override
        public <T> T unmarshalFrom(Object data, TypeRef<T> typeRef) {
            return jsonMapper.convertValue(data, typeRef);
        }

        @Override
        public Mono<Void> closeGracefully() {
            return Mono.fromRunnable(this::close);
        }

        @Override
        public void close() {
            closed = true;
            try {
                out.close();
            } catch (IOException e) {
                logger.warn("KeY MCP server: failed to close SSE stream of session {}: {}",
                    sessionId, e.getMessage());
            }
        }
    }
}
