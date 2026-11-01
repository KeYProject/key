/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.FlowLayout;
import java.io.IOException;
import javax.swing.*;

import org.key_project.key.llm.mcp.server.KeYMcpSseServer;

/**
 * Status-line indicator of the KeY MCP server: a toggle that starts/stops the SSE server (bound to
 * the host/port/token of {@link LlmSettings}) and a label that shows the endpoint MCP clients can
 * connect to while the server runs. The enabled flag of {@link LlmSettings} is kept in sync, so the
 * server is restored across KeY sessions; the toggle state and the endpoint label follow the server
 * lifecycle through the {@link KeYMcpSseServer.Listener}.
 *
 * @author Alexander Weigl
 */
public class LlmStatusBar extends JPanel {
    private final JToggleButton btnToggle = new JToggleButton("MCP");
    private final JLabel lblEndpoint = new JLabel();

    private KeYMcpSseServer server;
    private boolean restoreChecked;

    /** Creates the status-line component (must happen on the Swing event dispatch thread). */
    public LlmStatusBar() {
        super(new FlowLayout(FlowLayout.LEFT, 2, 0));
        setOpaque(false);
        btnToggle.setFocusable(false);
        btnToggle.setToolTipText("Start / stop the KeY MCP server (SSE). While it runs, MCP "
            + "clients such as Claude Desktop can connect to the endpoint shown next to it.");
        btnToggle.addActionListener(e -> toggle());
        lblEndpoint.setVisible(false);
        lblEndpoint.setBorder(BorderFactory.createEmptyBorder(0, 4, 0, 4));
        add(btnToggle);
        add(lblEndpoint);
    }

    /**
     * Restores the persisted server state once, when the status bar has been attached. Does
     * nothing if the MCP server was not enabled in the last session. Idempotent; called by the
     * status-line extension and by UI tests to replay a previously enabled server.
     */
    public void maybeRestore() {
        if (restoreChecked) {
            return;
        }
        restoreChecked = true;
        if (LlmSettings.INSTANCE.getMcpServerEnabled()) {
            SwingUtilities.invokeLater(this::startServer);
        }
    }

    private void toggle() {
        if (server != null) {
            server.stop();
        } else {
            startServer();
        }
    }

    /**
     * Starts the server with the current host/port/token settings; the listener reflects the state.
     */
    private void startServer() {
        var settings = LlmSettings.INSTANCE;
        var candidate =
            new KeYMcpSseServer(settings.getMcpServerHost(), settings.getMcpServerPort(),
                settings.getMcpServerToken());
        candidate.addListener(listener);
        server = candidate;
        try {
            candidate.start();
        } catch (IOException e) {
            server = null;
            settings.setMcpServerEnabled(false);
            JOptionPane.showMessageDialog(this,
                "The KeY MCP server could not be started:\n" + e.getMessage(),
                "KeY MCP server", JOptionPane.ERROR_MESSAGE);
        }
    }

    /** Keeps the toggle and the endpoint label in sync with the server lifecycle. */
    private final KeYMcpSseServer.Listener listener = new KeYMcpSseServer.Listener() {
        @Override
        public void started(KeYMcpSseServer s) {
            // called on the EDT from KeYMcpSseServer.start()
            if (s == server) {
                btnToggle.setSelected(true);
                String endpoint = s.getSseEndpoint();
                lblEndpoint.setText(endpoint);
                lblEndpoint.setToolTipText(
                    "The KeY MCP server endpoint. Configure it in your MCP client, e.g. as the"
                        + " 'url' of a Claude Desktop MCP server.");
                lblEndpoint.setVisible(true);
                LlmSettings.INSTANCE.setMcpServerEnabled(true);
            }
        }

        @Override
        public void stopped(KeYMcpSseServer s) {
            // called on the EDT from KeYMcpSseServer.stop()
            if (s == server) {
                server = null;
                btnToggle.setSelected(false);
                lblEndpoint.setVisible(false);
                LlmSettings.INSTANCE.setMcpServerEnabled(false);
            }
        }
    };
}
