package edu.kit.iti.formal.keyextclientjava;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;

import java.io.*;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.ReentrantLock;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (22.11.24)
 */
public final class RPCLayer {
    private final GsonBuilder builder = new GsonBuilder();
    // unclear whether concurrent use is possible
    private final Gson gson = builder.create();

    private final BufferedReader incoming;
    private final Writer outgoing;
    private final Thread threadListener;

    private ReentrantLock lockSend = new ReentrantLock();

    private final ConcurrentHashMap<String, Object> waiting = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<String, Object> responses = new ConcurrentHashMap<>();

    private AtomicInteger idCounter = new AtomicInteger();

    public Consumer<Object> allEventHandler = (o) -> {
    };

    public RPCLayer(Reader incoming, Writer outgoing) {
        this.incoming = new BufferedReader(incoming);
        this.outgoing = outgoing;
        threadListener = new Thread(this::listenForEvents);
        threadListener.start();
    }

    public static RPCLayer startWithCLI(String jarFile) throws IOException {
        var pbuilder = new ProcessBuilder("java", "-jar", jarFile);
        var p = pbuilder.start();
        var incoming = new InputStreamReader(p.getInputStream());
        var outgoing = new OutputStreamWriter(p.getOutputStream());
        return new RPCLayer(incoming, outgoing);
    }

    private void listenForEvents() {
        char[] buf = new char[4 * 1024];
        try {
            while (true) {
                String length = incoming.readLine();
                if (length == null) {
                    break; // connection closed
                }

                if (!length.startsWith("Content-Length: ")) {
                    break;//communication mismatch
                }

                int len = Integer.parseInt(length.substring(17));

                if (buf.length <= len + 2) {//also read \r\n,
                    buf = new char[len + 2]; //reallocate more
                }

                int count = incoming.read(buf);
                assert count == buf.length;

                var message = new String(buf, 0, count);
                processIncomingMessage(message);
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void processIncomingMessage(String message) {
        var simpleMap = gson.fromJson(message, Map.class);
    }

    public Object waitForResponse(String id) throws InterruptedException {
        var cond = waiting.get(id);
        cond.wait();
        return responses.get(id);
    }

    public Object callSync(String methodName, Object... args) throws InterruptedException, IOException {
        var id = nextId();
        waiting.put(id, new Object());
        sendAsync(id, methodName, args);
        return waitForResponse(id);
    }

    public void callAsync(String methodName, Object... args) throws IOException {
        var id = nextId();
        sendAsync(id, methodName, args);
    }

    private String nextId() {
        return "" + idCounter.getAndIncrement();
    }

    private void sendAsync(String id, String methodName, Object[] args) throws IOException {
        try {
            lockSend.lock();
            var map = Map.of("id", id, "method", methodName, "args", args);
            var json = gson.toJson(map);
            outgoing.write("Content-Length: %d\r\n".formatted(json.length()));
            outgoing.write(json);
            outgoing.write("\r\n");
            outgoing.flush();
        } finally {
            lockSend.unlock();
        }
    }
}