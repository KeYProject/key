/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.webctrl;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpServer;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.URLDecoder;
import java.nio.charset.Charset;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.Executor;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;


///
@KeYGuiExtension.Info(name = "webctrl", experimental = false,
        description = "Allows to control KeY via a local webserver.")
public class WebCtrlExtension implements KeYGuiExtension, KeYGuiExtension.StatusLine, KeYGuiExtension.Startup {
    public static final Logger LOGGER = LoggerFactory.getLogger(WebCtrlExtension.class);
    public static final int PORT = 8000;

    private @MonotonicNonNull MainWindow mainWindow;
    private @MonotonicNonNull KeYMediator mediator;
    private @MonotonicNonNull JCheckBox chkBoxOnOff = new JCheckBox("webctrl");
    private @Nullable HttpServer server;


    public WebCtrlExtension() {
    }

    public void init(MainWindow window, KeYMediator mediator) {
        LOGGER.info("Initializing WebCtrl Extension");

        this.mainWindow = window;
        this.mediator = mediator;

        chkBoxOnOff.addActionListener(evt -> {
            if (server == null && chkBoxOnOff.isSelected()) {
                try {
                    start();
                } catch (IOException e) {
                    LOGGER.error("Error starting webctrl server", e);
                }
            }

            if (server != null && !chkBoxOnOff.isSelected()) {
                stop();
            }
        });
    }

    private void stop() {
        if (server != null) {
            LOGGER.info("Tear down WebCtrl Extension");
            server.stop(0);
        }
    }

    private void start() throws IOException {
        assert server != null;

        LOGGER.info("Starting WebCtrl Extension at port {}", PORT);
        HttpServer server = HttpServer.create(new InetSocketAddress(PORT), 0);
        server.createContext("/openExample", new ExampleOpenerHandler(mainWindow, mediator));
        server.createContext("/select", new SelectHandler(mainWindow, mediator));

        server.setExecutor(Executors.newVirtualThreadPerTaskExecutor()); // creates a default executor
        server.start();
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return List.of(chkBoxOnOff);
    }


    /// Helper method to parse query string into a map
    public static Map<String, String> queryToMap(HttpExchange exchange) {
        String query = exchange.getRequestURI().getRawQuery();
        if (query == null) {
            return Map.of();
        }
        Map<String, String> result = new HashMap<>();
        for (String param : query.split("&")) {
            String[] entry = param.split("=");
            if (entry.length > 1) {
                result.put(
                        URLDecoder.decode(entry[0], Charset.defaultCharset()),
                        URLDecoder.decode(entry[1], Charset.defaultCharset())
                );
            } else {
                result.put(URLDecoder.decode(entry[0], Charset.defaultCharset()), "");
            }
        }
        return result;
    }
}
