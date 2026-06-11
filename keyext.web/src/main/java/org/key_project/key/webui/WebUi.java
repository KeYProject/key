package org.key_project.key.webui;

import org.eclipse.jetty.ee11.servlet.DefaultServlet;
import org.eclipse.jetty.ee11.servlet.ServletContextHandler;
import org.eclipse.jetty.ee11.websocket.jakarta.server.config.JakartaWebSocketServletContainerInitializer;
import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.util.resource.Resource;
import org.eclipse.jetty.util.resource.ResourceFactory;
import org.keyproject.key.api.StartServer;

public class WebUi {
    public static void main(String[] args) throws Exception {
        startNetty();
    }

    private static void startNetty() throws Exception {
        Server server = new Server(8080);
        ServletContextHandler context = new ServletContextHandler();
        context.setContextPath("/");

        // Static files from classpath
        ResourceFactory resourceFactory = ResourceFactory.of(context);
        Resource staticResources = resourceFactory.newClassLoaderResource("static");
        if (staticResources == null || !staticResources.exists()) {
            throw new IllegalStateException("Classpath resource 'static' not found");
        }
        context.setBaseResource(staticResources);

        // Enable Jakarta WebSocket
        JakartaWebSocketServletContainerInitializer.configure(context, (servletContext, wsContainer) -> {
            wsContainer.setDefaultMaxTextMessageBufferSize(128 * 1024);
            wsContainer.addEndpoint(JsonRpcWebSocketEndpoint.class);
        });

        // Serve static files
        context.addServlet(DefaultServlet.class, "/");

        server.setHandler(context);
        server.start();
        System.out.println("Server running at http://localhost:8080");
        server.join();
    }
}

