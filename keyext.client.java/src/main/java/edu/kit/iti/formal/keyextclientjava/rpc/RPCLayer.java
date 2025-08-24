/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package edu.kit.iti.formal.keyextclientjava.rpc;

import java.io.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (22.11.24)
 */
public final class RPCLayer {
    private final BufferedReader incoming;
    private final Writer outgoing;

    private @Nullable Thread threadListener;
    private @Nullable Thread threadMessageHandling;

    private final ConcurrentHashMap<String, SimpleFuture> waiting = new ConcurrentHashMap<>();
    public final ArrayBlockingQueue<JsonObject> incomingMessages = new ArrayBlockingQueue<>(16);

    private final AtomicInteger idCounter = new AtomicInteger();


    public RPCLayer(Reader incoming, Writer outgoing) {
        this.incoming = new BufferedReader(incoming);
        this.outgoing = outgoing;
    }

    public static RPCLayer startWithCLI(String jarFile) throws IOException {
        var pbuilder = new ProcessBuilder("java", "-jar", jarFile);
        var p = pbuilder.start();
        var incoming = new InputStreamReader(p.getInputStream());
        var outgoing = new OutputStreamWriter(p.getOutputStream());
        return new RPCLayer(incoming, outgoing);
    }

    public JsonObject waitForResponse(String id) throws InterruptedException, ExecutionException {
        var cond = waiting.get(id);
        var r = cond.get();
        waiting.remove(id);
        return r;
    }

    public JsonObject callSync(String methodName, Object... args) {
        var id = nextId();
        waiting.put(id, new SimpleFuture());
        try {
            sendAsync(id, methodName, args);
            var response = waitForResponse(id);
            return handleError(response);
        } catch (InterruptedException | IOException | ExecutionException e) {
            throw new RuntimeException(e);
        }
    }

    private JsonObject handleError(JsonObject response) {
        if (response.get("error") != null) {
            throw new RuntimeException("Request did not succeed " + response.get("error"));
        }
        return response;
    }

    public void callAsync(String methodName, Object... args) throws IOException {
        var id = nextId();
        sendAsync(id, methodName, args);
    }

    private String nextId() {
        return "" + idCounter.getAndIncrement();
    }

    private void sendAsync(String id, String methodName, Object[] args) throws IOException {
        var json = JsonRPC.createRequest(id, methodName, args);
        final var str = JsonRPC.addHeader(json);
        outgoing.write(str);
        outgoing.flush();
    }

    public void start() {
        threadListener =
            new Thread(new JsonStreamListener(incoming, incomingMessages), "JSON Message Reader");
        threadMessageHandling = new Thread(this::handler, "JSON Message Handler");
        threadListener.start();
        threadMessageHandling.start();
    }

    private void handler() {
        try {
            while (true) {
                var obj = incomingMessages.poll(1, TimeUnit.MINUTES);
                if (obj == null) {
                    continue;
                }
                if (obj.get("id") != null) {
                    var id = obj.get("id").getAsString();
                    var syncObj = waiting.get(id);
                    syncObj.put(obj);
                } else {
                    // TODO handle notification
                    System.out.println("Notification received");
                    System.out.println(obj);
                }
            }
        } catch (InterruptedException ignored) {
        }
    }

    public void dispose() {
        if (threadListener != null) {
            threadListener.interrupt();
        }
    }

    public static class JsonStreamListener implements Runnable {
        private final char[] CLENGTH = (JsonRPC.CONTENT_LENGTH + " ").toCharArray();
        private final PushbackReader incoming;
        private final ArrayBlockingQueue<JsonObject> incomingMessageQueue;
        /**
         * Internal buffer for reading efficient.
         */
        private char[] buf = new char[4 * 1024];

        public JsonStreamListener(Reader incoming, ArrayBlockingQueue<JsonObject> queue) {
            this.incoming = new PushbackReader(new BufferedReader(incoming)); // ensure bufferness
            this.incomingMessageQueue = queue;
        }

        @Override
        public void run() {
            try {
                while (true) {
                    final var message = readMessage();
                    if (message == null)
                        break;
                    final var jsonObject = JsonParser.parseString(message).getAsJsonObject();
                    incomingMessageQueue.add(jsonObject);
                }
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }

        protected void processIncomingMessage(String message) {

        }


        public @Nullable String readMessage() throws IOException {
            expectedContentLength();
            final var len = readLength() + 2; // also read \r\n,

            if (len == 2) {// EOF reached
                return null;
            }

            if (buf.length <= len) { // reallocate more if necessary
                buf = new char[len];
            }

            int count = incoming.read(buf, 0, len);
            assert count == len;
            consumeCRNL();
            return new String(buf, 0, count).trim();
        }

        private int readLength() throws IOException {
            int c;
            int len = 0;
            do {
                c = incoming.read();
                // if (Character.isWhitespace(c)) continue;
                if (c == -1)
                    return 0;
                if (c == '\r' || c == '\n')
                    break;
                if (Character.isDigit(c)) {
                    len = len * 10 + c - '0';
                } else {
                    throw new IllegalStateException("Expected: a digit, but got '%c'".formatted(c));
                }
            } while (c != -1);
            c = incoming.read(); // consume the '\n'
            assert c == '\n';
            return len;
        }

        private void expectedContentLength() throws IOException {
            for (var e : CLENGTH) {
                int c = incoming.read();
                if (c == -1)
                    return;
                if (e != c) {
                    throw new IllegalStateException("Expected: '%c', but got '%c'".formatted(e, c));
                }
            }
        }

        private void consumeCRNL() throws IOException {
            int c = incoming.read();
            if (c == '\r') {
                c = incoming.read();
                assert c == '\n';
            } else {
                incoming.unread(c);
            }
        }
    }
}


class SimpleFuture implements Future<JsonObject> {
    private final CountDownLatch latch = new CountDownLatch(1);
    private JsonObject value;

    @Override
    public boolean cancel(boolean mayInterruptIfRunning) {
        return false;
    }

    @Override
    public boolean isCancelled() {
        return false;
    }

    @Override
    public boolean isDone() {
        return value != null;
    }

    @Override
    public JsonObject get() throws InterruptedException, ExecutionException {
        latch.await();
        return value;
    }

    @Override
    public JsonObject get(long timeout, TimeUnit unit)
            throws InterruptedException, TimeoutException {
        if (latch.await(timeout, unit)) {
            return value;
        } else {
            throw new TimeoutException();
        }
    }

    void put(JsonObject value) {
        this.value = value;
        latch.countDown();
    }

}
