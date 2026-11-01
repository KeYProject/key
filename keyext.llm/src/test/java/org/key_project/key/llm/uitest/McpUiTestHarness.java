/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm.uitest;

import java.awt.Color;
import java.awt.Component;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.Graphics2D;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import javax.imageio.ImageIO;
import javax.swing.AbstractButton;
import javax.swing.JLabel;
import javax.swing.SwingUtilities;
import javax.swing.text.JTextComponent;

import org.key_project.key.llm.LlmSettings;
import org.key_project.key.llm.mcp.FunctionDefinition;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

/**
 * Shared helpers for the headless UI tests of the KeY MCP server: running tasks on the Swing event
 * dispatch thread, a small deterministic mock tool set, walking the component tree of a panel, and
 * rendering a component to a PNG (via {@code JComponent.print} into a {@link BufferedImage}, which
 * works without a display). See {@code docs/mcp-server-ui-testing.md} for the test protocol.
 */
public final class McpUiTestHarness {

    /* Mock tool names. */
    public static final String MOCK_AUTH = "mock_auth";
    public static final String MOCK_READ = "mock_read";
    public static final String MOCK_RUN = "mock_run";

    private McpUiTestHarness() {
    }

    /** Runs a task on the Swing event dispatch thread and blocks until it has completed. */
    public static void onEdt(Runnable task) {
        try {
            SwingUtilities.invokeAndWait(task);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new RuntimeException("interrupted while waiting for the EDT", e);
        } catch (InvocationTargetException e) {
            throw new RuntimeException(e.getCause());
        }
    }

    /** Resets every MCP-related setting of the global instance to a clean test state. */
    public static void resetSettings() {
        var s = LlmSettings.INSTANCE;
        s.setToolsDisabled(new TreeSet<>());
        s.setAllowedToolsWithApproval(new TreeSet<>());
        s.setAllowedToolsWithoutApproval(new TreeSet<>());
        s.setBackgroundToolsEnabled(new TreeSet<>());
        s.setBackgroundToolsDisabled(new TreeSet<>());
        s.setMcpExportedTools(new TreeSet<>());
        s.setMcpNotExportedTools(new TreeSet<>());
        s.setMcpServerEnabled(false);
        s.setMcpServerHost("127.0.0.1");
        s.setMcpServerPort(0);
        s.setMcpServerToken("");
    }

    /**
     * A small, deterministic tool set for UI tests: one auto-approved proof tool, one auto-approved
     * file tool and one ask-approved shell tool.
     */
    public static List<Tool> mockTools() {
        return List.of(
            new Tool(new FunctionDefinition(MOCK_AUTH, "an auto-approved mock proof tool"),
                Tool.ApprovalRequirement.AUTO, ToolCategory.PROOF, false),
            new Tool(new FunctionDefinition(MOCK_READ, "reads a mock file"),
                Tool.ApprovalRequirement.AUTO, ToolCategory.FILES, true),
            new Tool(new FunctionDefinition(MOCK_RUN, "runs a mock command"),
                Tool.ApprovalRequirement.ASK, ToolCategory.SHELL, true));
    }

    /**
     * All descendants of the given container of the given type, depth-first in their layout order
     * (so index {@code i} corresponds to the {@code i}-th matching component as a user sees it).
     */
    public static <T extends Component> List<T> all(Container root, Class<T> type) {
        var found = new ArrayList<T>();
        for (Component c : root.getComponents()) {
            if (type.isInstance(c)) {
                found.add(type.cast(c));
            }
            if (c instanceof Container child) {
                found.addAll(all(child, type));
            }
        }
        return found;
    }

    /** The widget text of a component, if it has one (labels, buttons, text components). */
    public static String textOf(Component c) {
        if (c instanceof JLabel l) {
            return l.getText();
        }
        if (c instanceof AbstractButton b) {
            return b.getText();
        }
        if (c instanceof JTextComponent t) {
            return t.getText();
        }
        return null;
    }

    /**
     * Renders the component into a PNG file and also returns the image, so callers can assert on
     * it. The component is laid out to a clamped preferred size first; rendering happens headless
     * via {@code JComponent.print}.
     */
    public static BufferedImage render(Component c, Path target) throws IOException {
        Dimension pref = c.getPreferredSize();
        int width = Math.max(360, Math.min(pref.width, 1200));
        int height = Math.max(120, Math.min(pref.height, 4800));
        c.setSize(width, height);
        // Headless components have no peers, so Container.validate() does not descend into the
        // tree; lay out every container explicitly instead (top-down, parents first).
        if (c instanceof Container container) {
            layoutRecursively(container);
        }
        var img = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);
        Graphics2D g = img.createGraphics();
        g.setColor(Color.WHITE);
        g.fillRect(0, 0, width, height);
        c.print(g);
        g.dispose();
        Files.createDirectories(target.getParent());
        ImageIO.write(img, "png", target.toFile());
        return img;
    }

    /** Lays out the container and all its descendants (parents first). */
    private static void layoutRecursively(Container c) {
        c.doLayout();
        for (Component child : c.getComponents()) {
            if (child instanceof Container childContainer) {
                layoutRecursively(childContainer);
            }
        }
    }
}
