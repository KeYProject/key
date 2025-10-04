package org.key_project.webctrl;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpHandler;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

import java.io.IOException;

class SelectHandler implements HttpHandler {
    public SelectHandler(@MonotonicNonNull MainWindow mainWindow, @MonotonicNonNull KeYMediator mediator) {
    }

    @Override
    public void handle(HttpExchange exchange) throws IOException {

    }
}
