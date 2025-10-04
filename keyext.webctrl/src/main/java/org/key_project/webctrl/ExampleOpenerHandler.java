package org.key_project.webctrl;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.MainWindow;
import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.InetAddress;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.function.Consumer;

@NullMarked
class ExampleOpenerHandler implements HttpHandler {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExampleOpenerHandler.class);
    private final MainWindow mainWindow;

    public ExampleOpenerHandler(MainWindow mainWindow,
                                KeYMediator mediator) {
        this.mainWindow = mainWindow;
    }

    @Override
    public void handle(HttpExchange exchange) throws IOException {
        var params = WebCtrlExtension.queryToMap(exchange);
        var name = params.get("name");
        WebCtrlExtension.LOGGER.info("Incoming request to open example {}", name);

        var ipv6 = InetAddress.getByName("::1");
        final var incomingAddress = exchange.getRemoteAddress().getAddress();
        if (!(incomingAddress.equals(InetAddress.getLocalHost())
                || incomingAddress.equals(ipv6))
        ) {
            WebCtrlExtension.LOGGER.warn("Incoming request does not comes frm loopback address ({}, {}) but from {}. Abort processing.",
                    ipv6, InetAddress.getLoopbackAddress(), incomingAddress);
            exchange.sendResponseHeaders(403, 0);
            exchange.close();
            return;
        }

        var examples =
                ExampleChooser.listExamples(ExampleChooser.lookForExamples());

        for (ExampleChooser.Example example : examples) {
            if (example.getName().equals(name)) {
                LOGGER.info("Found example: {}. KeY will open it.", example);
                SwingUtilities.invokeLater(() ->
                        mainWindow.loadProblem(example.getObligationFile().toPath()));
                exchange.sendResponseHeaders(200, 0);
                exchange.close();
                return;
            }
        }

        writeOverview(exchange, examples);
        exchange.getResponseBody().flush(); // so important
        exchange.getResponseBody().close();
    }

    private static void writeOverview(HttpExchange exchange, List<ExampleChooser.Example> examples) throws IOException {
        exchange.getResponseHeaders().add("Content-Type", "text/html");
        sendHtml(exchange, 200, (out) -> {
            out.println("""
                        <h1>Available Examples:</h1>
                        <ul>
                    """);
            for (ExampleChooser.Example example : examples) {
                out.format("<li><a href=\"/openExample?name=%s\">%s</a><pre>%s</pre></li>",
                        example.getName(), example.getName(), example.getDescription());
            }
            out.format("</ul>");
        });
    }

    private static void sendHtml(HttpExchange exchange, int status, Consumer<PrintWriter> c) throws IOException {
        StringWriter sw = new StringWriter(4 * 1024 * 1024);
        PrintWriter out = new PrintWriter(sw, false);
        out.format("<!DOCTYPE html><html><head></head><body>%n");
        c.accept(out);
        out.format("</body></html>");
        out.flush();
        out.close();
        var str = sw.toString();

        try {
            final var bytes = str.getBytes(StandardCharsets.UTF_8);
            exchange.sendResponseHeaders(status, bytes.length);
            System.out.println("ExampleOpenerHandler.sendHtml1");
            exchange.getResponseBody().write(bytes);
            System.out.println("ExampleOpenerHandler.sendHtml2");
            exchange.getResponseBody().flush(); // so important
            System.out.println("ExampleOpenerHandler.sendHtml3");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
