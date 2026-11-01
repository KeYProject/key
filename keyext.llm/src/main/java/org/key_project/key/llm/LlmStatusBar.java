/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.Color;
import java.awt.Cursor;
import java.awt.Toolkit;
import java.awt.datatransfer.StringSelection;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import javax.swing.BorderFactory;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.JToggleButton;
import javax.swing.SwingUtilities;
import javax.swing.Timer;
import javax.swing.UIManager;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

import org.key_project.key.llm.mcp.server.KeYMcpSseServer;

import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

/**
 * Minimal status-line indicator of the KeY MCP server: a flat, borderless toggle showing the text
 * {@code MCP} with a small circle dot in front of it — red while the server is off, green while it
 * runs. The endpoint URL MCP clients can connect to is only shown while the pointer hovers over
 * the indicator; it is displayed as a read-only text field (selectable, copyable with Ctrl+C) and
 * a click copies it to the clipboard, confirmed by a short "copied to clipboard" flash.
 * <p>
 * The toggle starts/stops the SSE server (bound to the host/port/token of {@link LlmSettings});
 * the enabled flag of {@link LlmSettings} is kept in sync, so the server is restored across KeY
 * sessions. The toggle state and the endpoint field follow the server lifecycle through the
 * {@link KeYMcpSseServer.Listener}.
 *
 * @author Alexander Weigl
 */
public class LlmStatusBar extends JPanel {

    /** Dot color while the server is off (red). */
    private static final Color COLOR_OFF = new Color(0xC62828);

    /** Dot color while the server is running (green). */
    private static final Color COLOR_ON = new Color(0x2E7D32);

    /** Subdued color of the endpoint hint text. */
    private static final Color COLOR_HINT =
        UIManager.getColor("Label.disabledForeground") == null ? Color.GRAY
                : UIManager.getColor("Label.disabledForeground");

    private KeYMcpSseServer server;
    private boolean restoreChecked;
    private boolean mouseOverIndicator;
    private String currentUrl = "";

    private final JToggleButton btnToggle = new JToggleButton("MCP");
    /** Read-only, selectable field showing the endpoint while hovered; click copies it. */
    private final JTextField txtEndpoint = new JTextField();
    /** Restores the URL text after the click-to-copy confirmation flash. */
    private final Timer copyFeedback = new Timer(900, e -> {
        txtEndpoint.setText(currentUrl);
        updateEndpointVisibility();
    });

    /** Creates the status-line component (must happen on the Swing event dispatch thread). */
    public LlmStatusBar() {
        // baseline-aligned: the toggle and the endpoint field sit on the text baseline of the
        // surrounding status line. Baseline alignment must be set per component (CC); on the
        // layout (LC) it would set the row alignment, which MigLayout cannot handle.
        super(new MigLayout(new LC().insets("0")));
        setOpaque(false);

        btnToggle.setFocusable(false);
        btnToggle.setRequestFocusEnabled(false);
        btnToggle.setOpaque(false);
        btnToggle.setContentAreaFilled(false);
        btnToggle.setBorderPainted(false);
        btnToggle.setFocusPainted(false);
        btnToggle.setBorder(BorderFactory.createEmptyBorder(3, 6, 3, 6));
        btnToggle.setCursor(Cursor.getPredefinedCursor(Cursor.HAND_CURSOR));
        btnToggle.addActionListener(e -> toggle());
        add(btnToggle, new CC().alignY("baseline"));

        txtEndpoint.setVisible(false);
        txtEndpoint.setEditable(false);
        txtEndpoint.setOpaque(false);
        txtEndpoint.setForeground(COLOR_HINT);
        txtEndpoint.setBorder(BorderFactory.createEmptyBorder(3, 2, 3, 8));
        txtEndpoint.setCursor(Cursor.getPredefinedCursor(Cursor.TEXT_CURSOR));
        txtEndpoint.setToolTipText("The KeY MCP server endpoint; configure it in your MCP client,"
            + " e.g. as the 'url' of a Claude Desktop MCP server. Select it or click to copy it to"
            + " the clipboard.");
        txtEndpoint.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                copyEndpoint();
            }
        });
        add(txtEndpoint, new CC().alignY("baseline"));

        // the endpoint is hover-only: track the pointer over the whole indicator (toggle + field),
        // so moving from the toggle onto the URL keeps it visible
        var hoverTracker = new MouseAdapter() {
            @Override
            public void mouseEntered(MouseEvent e) {
                mouseOverIndicator = true;
                updateEndpointVisibility();
            }

            @Override
            public void mouseExited(MouseEvent e) {
                mouseOverIndicator = false;
                updateEndpointVisibility();
            }
        };
        addMouseListener(hoverTracker);
        btnToggle.addMouseListener(hoverTracker);
        txtEndpoint.addMouseListener(hoverTracker);

        copyFeedback.setRepeats(false);
        refreshLook();
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
            refreshLook();
            JOptionPane.showMessageDialog(this,
                "The KeY MCP server could not be started:\n" + e.getMessage(),
                "KeY MCP server", JOptionPane.ERROR_MESSAGE);
        }
    }

    /**
     * The endpoint URL is only shown while the server runs and the pointer hovers over the
     * indicator, or while a copy-confirmation flash is active.
     */
    private void updateEndpointVisibility() {
        boolean show = server != null && (mouseOverIndicator || copyFeedback.isRunning());
        txtEndpoint.setVisible(show);
        revalidate();
        repaint();
    }

    /** Applies the state-dependent look: red/green dot and tooltip; the text stays minimal. */
    private void refreshLook() {
        boolean running = server != null;
        btnToggle.setIcon(IconFontSwing.buildIcon(FontAwesomeSolid.CIRCLE, 10f,
            running ? COLOR_ON : COLOR_OFF));
        btnToggle.setToolTipText(running
                ? "The KeY MCP server is running (" + currentUrl + "). Hover to see the endpoint;"
                    + " click to stop it."
                : "Start the KeY MCP server (SSE). While it runs, MCP clients such as Claude Desktop"
                    + " can connect to the endpoint shown on hover.");
    }

    /** Copies the endpoint URL to the system clipboard and flashes a short confirmation. */
    private void copyEndpoint() {
        if (currentUrl.isBlank()) {
            return;
        }
        var selection = new StringSelection(currentUrl);
        Toolkit.getDefaultToolkit().getSystemClipboard().setContents(selection, selection);
        txtEndpoint.setText("copied to clipboard");
        copyFeedback.restart();
    }

    /** Keeps the toggle and the endpoint field in sync with the server lifecycle. */
    private final KeYMcpSseServer.Listener listener = new KeYMcpSseServer.Listener() {
        @Override
        public void started(KeYMcpSseServer s) {
            // called on the EDT from KeYMcpSseServer.start()
            if (s == server) {
                btnToggle.setSelected(true);
                currentUrl = s.getSseEndpoint();
                txtEndpoint.setText(currentUrl);
                txtEndpoint.setColumns(currentUrl.length());
                LlmSettings.INSTANCE.setMcpServerEnabled(true);
                refreshLook();
                updateEndpointVisibility();
            }
        }

        @Override
        public void stopped(KeYMcpSseServer s) {
            // called on the EDT from KeYMcpSseServer.stop()
            if (s == server) {
                server = null;
                copyFeedback.stop();
                btnToggle.setSelected(false);
                txtEndpoint.setVisible(false);
                LlmSettings.INSTANCE.setMcpServerEnabled(false);
                refreshLook();
            }
        }
    };
}
