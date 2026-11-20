/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.BorderLayout;
import java.awt.CardLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dialog;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Window;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import javax.swing.BorderFactory;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JToggleButton;
import javax.swing.JTree;
import javax.swing.SwingUtilities;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeCellRenderer;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import org.key_project.key.llm.mcp.BuiltInMCPClient;
import org.key_project.key.llm.mcp.Tool;
import org.key_project.key.llm.mcp.ToolCategory;

import net.miginfocom.swing.MigLayout;
import org.jspecify.annotations.Nullable;

/**
 * A manual tool console: pick one of the agent tools, compose its arguments with a generated
 * form or as raw JSON, and call it against the live environment (the open proof, the real
 * settings). It is the interactive counterpart to the agent chat and calls through the same
 * {@link BuiltInMCPClient}: approval requirements, persisted approvals and the stringified
 * results ({@link AgentLoop#stringify(Object)}) are exactly what the model would see.
 * <p>
 * ASK-tools are gated by a {@link ToolApprovalPrompt}; <em>Always allow</em> persists the
 * approval like the chat does. Calls run on a worker thread; the last {@value #HISTORY_LIMIT}
 * calls are kept in memory and can be re-loaded into the editor.
 *
 * @author Alexander Weigl
 */
public class ToolConsoleDialog extends JDialog {

    /** The number of recent calls kept in the in-memory history. */
    public static final int HISTORY_LIMIT = 20;

    private static final String CARD_FORMS = "forms";
    private static final String CARD_JSON = "json";

    private final BuiltInMCPClient client;

    private final ToolApprovalPrompt prompt;

    private final JTextField txtSearch = new JTextField();
    private final JTree treeTools = new JTree();
    private final JTextArea txtDescription = new JTextArea();
    private final JToggleButton btnForms = new JToggleButton("Forms");
    private final JToggleButton btnJson = new JToggleButton("JSON");
    private final JPanel pnlCards = new JPanel(new CardLayout());
    private final JTextArea txtJson = new JTextArea();
    private final JButton btnCall = new JButton("Call");
    private final JLabel lblStatus = new JLabel(" ");
    private final JTextArea txtResult = new JTextArea();
    private final JList<HistoryEntry> lstHistory = new JList<>();

    /** The currently selected tool ({@code null} until a tool leaf is selected). */
    private @Nullable Tool selectedTool;

    /** The generated parameter form of {@link #selectedTool}. */
    private @Nullable JsonSchemaForm currentForm;

    /** Whether the forms card or the raw-JSON card is visible. */
    private boolean formMode = true;

    /** Guards against re-entrant action events while toggling programmatically. */
    private boolean switchingMode;

    /** The recent calls, most recent first, bounded by {@link #HISTORY_LIMIT}. */
    private final Deque<HistoryEntry> history = new ArrayDeque<>();

    /**
     * Creates the console.
     *
     * @param owner the window to center on and to keep in front of; may be {@code null}
     * @param client the tool registry the console calls (the production registry shares the
     *        approval settings with the agent chat)
     */
    public ToolConsoleDialog(@Nullable Window owner, BuiltInMCPClient client) {
        this(owner, client, new ToolApprovalPrompt.Modal(owner));
    }

    /**
     * Creates the console with an injected approval prompt (used by tests to record decisions).
     */
    public ToolConsoleDialog(@Nullable Window owner, BuiltInMCPClient client,
            ToolApprovalPrompt prompt) {
        super(owner, "Tool Console", Dialog.ModalityType.MODELESS);
        this.client = client;
        this.prompt = prompt;
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        buildUi();
        rebuildTree();
    }

    // ------------------------------------------------------------------ construction

    /** Builds the whole layout: search, tool tree, description, editor cards, call, result. */
    private void buildUi() {
        getContentPane().setLayout(new BorderLayout(8, 8));
        ((JPanel) getContentPane()).setBorder(BorderFactory.createEmptyBorder(8, 10, 8, 10));

        // north: the search field drives the tool tree
        var north = new JPanel(new MigLayout("ins 0, fillx, wrap 2", "[]8[grow]"));
        north.add(new JLabel("Search:"));
        north.add(txtSearch, "growx");
        var docListener = new javax.swing.event.DocumentListener() {
            @Override
            public void insertUpdate(javax.swing.event.DocumentEvent e) {
                rebuildTree();
            }

            @Override
            public void removeUpdate(javax.swing.event.DocumentEvent e) {
                rebuildTree();
            }

            @Override
            public void changedUpdate(javax.swing.event.DocumentEvent e) {
                rebuildTree();
            }
        };
        txtSearch.getDocument().addDocumentListener(docListener);
        getContentPane().add(north, BorderLayout.NORTH);

        // left: the tool tree, grouped by category
        treeTools.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        treeTools.setCellRenderer(new ToolCellRenderer());
        treeTools.addTreeSelectionListener(e -> {
            var path = e.getNewLeadSelectionPath();
            if (toolOf(path) instanceof Tool tool) {
                selectTool(tool);
            }
        });
        var treeScroll = new JScrollPane(treeTools);
        treeScroll.setPreferredSize(new Dimension(250, 450));

        // right: description, mode toggle with inline status, editor cards, call, result
        txtDescription.setEditable(false);
        txtDescription.setLineWrap(true);
        txtDescription.setWrapStyleWord(true);
        var descriptionScroll = new JScrollPane(txtDescription);
        descriptionScroll.setPreferredSize(new Dimension(560, 64));

        var modeGroup = new ButtonGroup();
        modeGroup.add(btnForms);
        modeGroup.add(btnJson);
        btnForms.setSelected(true);
        btnForms.addActionListener(e -> switchMode());
        btnJson.addActionListener(e -> switchMode());
        var modeRow = new JPanel(new BorderLayout(8, 0));
        var buttons = new JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT, 4, 0));
        buttons.add(btnForms);
        buttons.add(btnJson);
        modeRow.add(buttons, BorderLayout.WEST);
        lblStatus.setForeground(Color.GRAY.darker());
        modeRow.add(lblStatus, BorderLayout.CENTER);

        txtJson.setFont(new Font(Font.MONOSPACED, Font.PLAIN, txtJson.getFont().getSize()));
        txtJson.setLineWrap(true);
        txtJson.setWrapStyleWord(false);

        var middle = new JPanel(new BorderLayout(0, 4));
        middle.add(modeRow, BorderLayout.NORTH);
        middle.add(pnlCards, BorderLayout.CENTER);

        btnCall.addActionListener(e -> invokeCall());
        var callRow = new JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.RIGHT, 4, 0));
        callRow.add(btnCall);

        txtResult.setEditable(false);
        txtResult.setFont(new Font(Font.MONOSPACED, Font.PLAIN, txtResult.getFont().getSize()));
        txtResult.setLineWrap(true);
        txtResult.setWrapStyleWord(true);
        var resultScroll = new JScrollPane(txtResult);
        resultScroll.setPreferredSize(new Dimension(560, 200));

        var lower = new JPanel(new BorderLayout(0, 4));
        lower.add(callRow, BorderLayout.NORTH);
        lower.add(resultScroll, BorderLayout.CENTER);

        var right = new JPanel(new BorderLayout(8, 8));
        right.add(descriptionScroll, BorderLayout.NORTH);
        right.add(middle, BorderLayout.CENTER);
        right.add(lower, BorderLayout.SOUTH);

        var split = new javax.swing.JSplitPane(javax.swing.JSplitPane.HORIZONTAL_SPLIT,
            treeScroll, right);
        split.setResizeWeight(0.0);
        getContentPane().add(split, BorderLayout.CENTER);

        // south: the in-memory call history
        lstHistory.setSelectionMode(javax.swing.ListSelectionModel.SINGLE_SELECTION);
        lstHistory.setCellRenderer((list, value, index, selected, focus) -> new JLabel(
            value.display()));
        lstHistory.addListSelectionListener(e -> {
            if (!e.getValueIsAdjusting() && lstHistory.getSelectedValue() != null) {
                loadHistoryEntry(lstHistory.getSelectedValue());
            }
        });
        var south = new JPanel(new BorderLayout(0, 2));
        south.add(new JLabel("Last calls (click to reload the tool and arguments):"),
            BorderLayout.NORTH);
        var historyScroll = new JScrollPane(lstHistory);
        historyScroll.setPreferredSize(new Dimension(860, 90));
        south.add(historyScroll, BorderLayout.CENTER);
        getContentPane().add(south, BorderLayout.SOUTH);

        setSize(920, 680);
    }

    /** The tool of a selection path, or {@code null} for category nodes. */
    private @Nullable Tool toolOf(@Nullable TreePath path) {
        if (path == null
                || !(path.getLastPathComponent() instanceof DefaultMutableTreeNode node)) {
            return null;
        }
        return node.getUserObject() instanceof Tool tool ? tool : null;
    }

    /** Renderer showing {@code name [auto|ask]} leaves and disabled tools. */
    private class ToolCellRenderer extends DefaultTreeCellRenderer {
        @Override
        public Component getTreeCellRendererComponent(JTree tree, Object value, boolean selected,
                boolean expanded, boolean leaf, int row, boolean focus) {
            var label = (JLabel) super.getTreeCellRendererComponent(tree, value, selected,
                expanded, leaf, row, focus);
            if (value instanceof DefaultMutableTreeNode node
                    && node.getUserObject() instanceof Tool tool) {
                label.setText(leafLabel(tool));
            }
            return label;
        }
    }

    /** The tree label of one tool: name, approval badge, disabled marker. */
    String leafLabel(Tool tool) {
        var name = tool.function().name();
        var label = name + (client.requiresApproval(name) ? " [ask]" : " [auto]");
        return client.isDisabled(name) ? label + " [disabled]" : label;
    }

    // ------------------------------------------------------------------ tool tree

    /** Rebuilds the tool tree from the current search query; all branches stay expanded. */
    void rebuildTree() {
        var query = txtSearch.getText().strip().toLowerCase();
        var root = new DefaultMutableTreeNode("Tools");
        var grouped = new LinkedHashMap<ToolCategory, List<Tool>>();
        client.getAllTools().stream()
                .filter(t -> query.isEmpty() || matchesQuery(t, query))
                .sorted(Comparator.comparing((Tool t) -> t.category().ordinal())
                        .thenComparing(t -> t.function().name()))
                .forEach(tool -> grouped.computeIfAbsent(tool.category(), c -> new ArrayList<>())
                        .add(tool));
        grouped.forEach((category, tools) -> {
            var categoryNode = new DefaultMutableTreeNode(category.label());
            tools.forEach(tool -> categoryNode.add(new DefaultMutableTreeNode(tool, false)));
            root.add(categoryNode);
        });
        treeTools.setModel(new DefaultTreeModel(root));
        for (int row = 0; row < treeTools.getRowCount(); row++) {
            treeTools.expandRow(row);
        }
    }

    /** Whether the tool's name, description or category label matches the search query. */
    private static boolean matchesQuery(Tool tool, String query) {
        return tool.function().name().toLowerCase().contains(query)
                || (tool.function().description() != null
                        && tool.function().description().toLowerCase().contains(query))
                || tool.category().label().toLowerCase().contains(query);
    }

    // ------------------------------------------------------------------ tool selection

    /** Shows the given tool's description and builds its parameter form. */
    void selectTool(Tool tool) {
        selectedTool = tool;
        txtDescription.setText(Objects.requireNonNullElse(tool.function().description(), ""));
        txtDescription.setCaretPosition(0);
        currentForm = new JsonSchemaForm(tool.function().parameters());
        pnlCards.removeAll();
        var formScroll = new JScrollPane(currentForm);
        formScroll.setBorder(BorderFactory.createEmptyBorder());
        var jsonScroll = new JScrollPane(txtJson);
        jsonScroll.setBorder(BorderFactory.createEmptyBorder());
        pnlCards.add(formScroll, CARD_FORMS);
        pnlCards.add(jsonScroll, CARD_JSON);
        setStatus(" ");
        try {
            txtJson.setText(currentForm.toArgumentsJson());
        } catch (IllegalStateException e) {
            txtJson.setText("{}");
        }
        formMode = true;
        selectQuietly(btnForms);
        showCard(CARD_FORMS);
        pnlCards.revalidate();
        pnlCards.repaint();
    }

    // ------------------------------------------------------------------ mode switching

    /** Applies a Forms|JSON toggle; a failed conversion reports inline and keeps the old mode. */
    private void switchMode() {
        if (switchingMode || currentForm == null) {
            return;
        }
        var form = currentForm;
        if (btnForms.isSelected() && !formMode) {
            // JSON → Forms: parse the document into the editors
            var error = form.fromArgumentsJson(txtJson.getText());
            if (error != null) {
                setStatus(error);
                selectQuietly(btnJson);
                return;
            }
            formMode = true;
            showCard(CARD_FORMS);
            setStatus(" ");
        } else if (btnJson.isSelected() && formMode) {
            // Forms → JSON: serialize the editors into the document
            try {
                txtJson.setText(form.toArgumentsJson());
            } catch (IllegalStateException e) {
                setStatus(e.getMessage());
                selectQuietly(btnForms);
                return;
            }
            formMode = false;
            showCard(CARD_JSON);
            setStatus(" ");
        }
    }

    /** Selects a toggle button without firing the mode switch again. */
    private void selectQuietly(JToggleButton button) {
        switchingMode = true;
        button.setSelected(true);
        switchingMode = false;
    }

    private void showCard(String card) {
        ((CardLayout) pnlCards.getLayout()).show(pnlCards, card);
    }

    /** The current arguments document, or {@code null} if it cannot be built (reported inline). */
    private @Nullable String currentArguments() {
        if (!formMode) {
            var text = txtJson.getText().strip();
            return text.isEmpty() ? "{}" : text;
        }
        var form = currentForm;
        if (form == null) {
            return null;
        }
        try {
            return form.toArgumentsJson();
        } catch (IllegalStateException e) {
            setStatus(e.getMessage());
            return null;
        }
    }

    private void setStatus(String text) {
        lblStatus.setText(text);
    }

    // ------------------------------------------------------------------ calling

    /**
     * Runs the selected tool: builds the arguments, consults the approval gate for ASK-tools and
     * then calls {@code callTool} on a worker thread. The result is delivered on the EDT.
     */
    private void invokeCall() {
        var tool = selectedTool;
        if (tool == null || currentForm == null) {
            return;
        }
        var name = tool.function().name();
        var arguments = currentArguments();
        if (arguments == null) {
            return;
        }

        // approval gate: identical policy and persistence as the agent chat
        if (client.requiresApproval(name)) {
            var decision = prompt.ask(name, arguments);
            if (decision == ToolApprovalPrompt.Decision.DENY) {
                showResult(false, 0, "[Tool call denied by the user: " + name + "]");
                return;
            }
            if (decision == ToolApprovalPrompt.Decision.ALWAYS) {
                client.allowWithoutApproval(name);
                rebuildTree();
                // keep the tree selection and the edited arguments (reselecting rebuilds them)
                selectTool(tool);
                restoreArguments(arguments);
            }
        }

        btnCall.setEnabled(false);
        setStatus("running " + name + "…");
        var start = System.nanoTime();
        new Thread(() -> {
            String out;
            boolean ok;
            try {
                out = AgentLoop.stringify(client.callTool(name, arguments));
                ok = true;
            } catch (Throwable t) {
                out = Objects.requireNonNullElse(t.getMessage(), t.toString());
                ok = false;
            }
            // final copies for the EDT lambda (try/catch-assigned locals are not effectively final)
            final var output = out;
            final var success = ok;
            final var durationMs = (System.nanoTime() - start) / 1_000_000;
            SwingUtilities.invokeLater(() -> {
                showResult(success, durationMs, output);
                addHistory(new HistoryEntry(name, arguments, success, durationMs));
                btnCall.setEnabled(true);
                setStatus(" ");
            });
        }, "tool-console-call").start();
    }

    /** Puts an arguments document back into the editor of the active mode. */
    private void restoreArguments(String arguments) {
        var form = currentForm;
        if (formMode && form != null) {
            form.fromArgumentsJson(arguments);
        } else {
            txtJson.setText(arguments);
        }
    }

    /** Shows the outcome of a call: a badge line with the duration and the raw output. */
    private void showResult(boolean success, long durationMs, String output) {
        txtResult.setText((success ? "✓ " : "✗ ") + durationMs + " ms\n" + output);
        txtResult.setCaretPosition(0);
    }

    // ------------------------------------------------------------------ history

    /** Appends a completed call to the history (most recent first, bounded). */
    private void addHistory(HistoryEntry entry) {
        history.addFirst(entry);
        while (history.size() > HISTORY_LIMIT) {
            history.removeLast();
        }
        lstHistory.setListData(history.toArray(new HistoryEntry[0]));
    }

    /** Loads a history entry back into the editor (only if the tool still exists). */
    private void loadHistoryEntry(HistoryEntry entry) {
        var tool = client.getAllTools().stream()
                .filter(t -> entry.tool().equals(t.function().name())).findFirst().orElse(null);
        if (tool == null) {
            setStatus("tool '" + entry.tool() + "' is no longer available");
            return;
        }
        selectTool(tool);
        restoreArguments(entry.arguments());
    }

    /** One executed (or denied) tool call, as recorded in the history. */
    record HistoryEntry(String tool, String arguments, boolean success, long durationMs) {
        String display() {
            return tool + " " + (success ? "✓" : "✗") + " " + durationMs + " ms";
        }
    }

    // ------------------------------------------------------------------ test accessors

    JTree toolTree() {
        return treeTools;
    }

    JTextField searchField() {
        return txtSearch;
    }

    JTextArea descriptionArea() {
        return txtDescription;
    }

    JToggleButton formsToggle() {
        return btnForms;
    }

    JToggleButton jsonToggle() {
        return btnJson;
    }

    JTextArea jsonArea() {
        return txtJson;
    }

    JButton callButton() {
        return btnCall;
    }

    JTextArea resultArea() {
        return txtResult;
    }

    /** The inline status/error label next to the mode toggles (for tests). */
    JLabel statusLabel() {
        return lblStatus;
    }

    JList<HistoryEntry> historyList() {
        return lstHistory;
    }

    @Nullable
    JsonSchemaForm currentForm() {
        return currentForm;
    }

    @Nullable
    Tool selectedTool() {
        return selectedTool;
    }

    /** The in-memory history, most recent first (for tests). */
    List<HistoryEntry> history() {
        return new ArrayList<>(history);
    }

    /** Selects the tree node of the named tool, if present (for tests). */
    boolean selectToolByName(String name) {
        for (int row = 0; row < treeTools.getRowCount(); row++) {
            var path = treeTools.getPathForRow(row);
            if (toolOf(path) instanceof Tool tool && tool.function().name().equals(name)) {
                treeTools.setSelectionPath(path);
                return true;
            }
        }
        return false;
    }
}
