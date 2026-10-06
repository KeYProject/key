/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.net.URI;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.docking.DynamicCMenu;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CMenu;
import bibliothek.gui.dock.common.action.CRadioButton;
import bibliothek.gui.dock.common.action.CRadioGroup;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * The KeY-Agent chat panel. It is deliberately thin: prompt assembly lives in
 * {@link ExtendedPrompt}, the agent turn is driven by {@link AgentLoop} and the markup in the
 * input box is resolved by {@link PromptResolver}. This panel only collects input, renders the
 * conversation, asks for tool approvals and relays answers to the agent's questions.
 * <p>
 * A turn is started on a background thread; whenever the loop pauses (question or approval) the
 * corresponding box is added and the turn is resumed with the user's decision.
 *
 * @author Alexander Weigl
 */
public class LlmPrompt extends JPanel implements TabPanel {
    private static final org.slf4j.Logger LOGGER =
        org.slf4j.LoggerFactory.getLogger(LlmPrompt.class);

    public static final ColorSettings.ColorProperty COLOR_BG_INPUT = ColorSettings.define(
        "llm.output.bg.input", "Background color in chat of LLM answers", new Color(130, 180, 220));
    public static final ColorSettings.ColorProperty COLOR_BG_ERROR = ColorSettings.define(
        "llm.output.bg.error", "Background color in chat of LLM answers", new Color(255, 180, 180));
    public static final ColorSettings.ColorProperty COLOR_BG_ANSWER = ColorSettings.define(
        "llm.output.bg.answer", "Background color in chat of LLM answers",
        new Color(230, 230, 230));
    public static final ColorSettings.ColorProperty COLOR_BG_ACTION = ColorSettings.define(
        "llm.output.bg.action", "Background color of question/approval boxes",
        new Color(255, 244, 200));

    private final JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
    private final AutocompleteInput txtInput = new AutocompleteInput();
    private final JPanel pOutput =
        new JPanel(new MigLayout(new LC().fillX().topToBottom().wrapAfter(1)));
    private final JScrollPane scrpOutput = new JScrollPane(pOutput);

    private final KeyAction actionSwitchOrientation = new SwitchOrientationAction();
    private final JButton btnStop = new JButton("Stop");
    private final JCheckBox chkProofContext = new JCheckBox("attach proof context");
    private final JPanel tblFiles = new JPanel(new MigLayout(new LC().fillX().wrapAfter(1)));

    private final MainWindow mainWindow;
    private final KeYMediator mediator;

    /** The active agent turn, or {@code null} when idle. */
    private @Nullable AgentLoop activeLoop;
    private boolean running = false;

    public LlmPrompt(MainWindow mainWindow, @NonNull KeYMediator mediator) {
        this.mainWindow = mainWindow;
        this.mediator = mediator;

        setLayout(new BorderLayout());
        add(buildToolbar(), BorderLayout.NORTH);

        scrpOutput.getVerticalScrollBar().setUnitIncrement(16);
        splitPane.add(scrpOutput);

        txtInput.addProvider(AutocompleteProviders.contextTokens());
        txtInput.addProvider(AutocompleteProviders.files());
        txtInput.addProvider(AutocompleteProviders.commands(this::openLibrarySettings,
            this::openLibrarySettings));

        var inputPane = new JPanel(new BorderLayout());
        inputPane.add(new JScrollPane(txtInput), BorderLayout.CENTER);
        var hint = new JLabel("Ctrl+Enter to send");
        hint.setForeground(Color.GRAY);
        hint.setBorder(BorderFactory.createEmptyBorder(0, 4, 2, 4));
        inputPane.add(hint, BorderLayout.SOUTH);

        var tabInputPanes = new JTabbedPane();
        tabInputPanes.addTab("Prompt", inputPane);
        var scrpFiles = new JScrollPane(tblFiles);
        tabInputPanes.addTab("Files", scrpFiles);
        splitPane.add(tabInputPanes);
        add(splitPane, BorderLayout.CENTER);

        txtInput.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_ENTER,
            InputEvent.CTRL_DOWN_MASK), "sendPrompt");
        txtInput.getActionMap().put("sendPrompt", new SendPromptAction());
        // Ctrl+Space expands the $token / @file / /directive at the caret in place.
        txtInput.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_SPACE,
            InputEvent.CTRL_DOWN_MASK), "expandAtCaret");
        txtInput.getActionMap().put("expandAtCaret",
            new KeyAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    expandAtCaret();
                }
            });

        populateFiles();

        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                populateFilesIfWritable();
            }
        });
    }

    private JComponent buildToolbar() {
        var toolbar = new JToolBar();
        toolbar.setFloatable(false);
        btnStop.setEnabled(false);
        btnStop.addActionListener(e -> {
            if (activeLoop != null) {
                activeLoop.cancel();
            }
            setRunning(false);
        });
        chkProofContext.addActionListener(e -> {
            var session = LlmUtils.getSession(mediator.getSelectedProof());
            session.setAttachProofContext(chkProofContext.isSelected());
        });
        toolbar.add(chkProofContext);
        toolbar.add(new JButton(new PromptsMenuAction()));
        toolbar.add(Box.createHorizontalGlue());
        toolbar.add(new JButton(new ClearHistoryAction()));
        toolbar.add(btnStop);
        return toolbar;
    }

    private @Nullable String activeSkillOfCurrentSession() {
        return LlmUtils.getSession(mediator.getSelectedProof()).getActiveSkill();
    }

    /**
     * Opens the settings dialog at the LLM node, where the prompt and skill libraries are managed.
     */
    private void openLibrarySettings() {
        SettingsManager.getInstance().showSettingsDialog(mainWindow,
            LlmExtension.LlmSettingsProvider.INSTANCE);
    }

    /**
     * Replaces the {@code $token}/{@code @file}/{@code /directive} before the caret with its
     * currently resolved content (Ctrl+Space). Unknown {@code $tokens} and bare activation
     * directives stay untouched.
     */
    private void expandAtCaret() {
        var session = LlmUtils.getSession(mediator.getSelectedProof());
        var context = new PromptResolver.Context() {
            @Override
            public @Nullable Proof proof() {
                return mediator.getSelectedProof();
            }

            @Override
            public @Nullable Node node() {
                return mediator.getSelectedNode();
            }
        };
        txtInput.expandAtCaret(fragment -> fragment.startsWith("$")
                ? PromptResolver.token(fragment.substring(1), session, context)
                : resolveDirective(fragment, session, context));
    }

    private static @Nullable String resolveDirective(String fragment, LlmSession session,
            PromptResolver.Context context) {
        var resolved = PromptResolver.resolve(fragment, session, context);
        return resolved.text().isBlank() ? null : resolved.text();
    }

    /** (Re)builds the Files tab from the bounded model file listing. */
    void populateFilesIfWritable() {
        if (SwingUtilities.isEventDispatchThread()) {
            populateFiles();
        } else {
            SwingUtilities.invokeLater(this::populateFiles);
        }
    }

    private void populateFiles() {
        try {
            tblFiles.removeAll();
            var proof = mediator.getSelectedProof();
            var session = LlmUtils.getSession(proof);
            var possible = new ArrayList<>(FileAccess.listFiles(proof));
            possible.sort(Comparator.comparing(Path::toString));
            Set<URI> selectedFiles = session.getSelectedFiles();
            int limit = Math.max(1, LlmSettings.INSTANCE.getMaxModelListingEntries());
            var shown = 0;
            for (var path : possible) {
                shown++;
                if (shown > limit) {
                    break;
                }
                var chk = new JCheckBox(new CheckBoxFileAction(path.toUri(), selectedFiles));
                chk.setLabel(path.getFileName().toString());
                tblFiles.add(chk);
            }
            if (shown > limit) {
                tblFiles.add(new JLabel("(listing truncated at " + limit + " entries)"));
            }
            tblFiles.invalidate();
            tblFiles.revalidate();
            tblFiles.repaint();
        } catch (Exception e) {
            LOGGER.warn("Could not populate the file list", e);
        }
    }

    // ------------------------------------------------------------------ rendering helpers

    private OutputBox<String> addInput(String text) {
        var o = addBox(new LlmPromptModel<>(LlmPromptModel.Kind.INPUT, text, text),
            new RepromptAction(text));
        o.setBackground(COLOR_BG_INPUT.get());
        return o;
    }

    private void addOutput(String text) {
        var o = addBox(new LlmPromptModel<>(LlmPromptModel.Kind.OUTPUT, text,
            new LlmContext.LlmMessage("assistant", text)));
        o.setBackground(COLOR_BG_ANSWER.get());
    }

    private void addError(String text) {
        var o = addBox(new LlmPromptModel<>(LlmPromptModel.Kind.ERROR, text, null));
        o.setBackground(COLOR_BG_ERROR.get());
    }

    private <T> OutputBox<T> addBox(LlmPromptModel<T> data, Action... actions) {
        var box = new OutputBox<>(data);
        for (Action it : actions) {
            box.menu.add(it);
        }
        pOutput.add(box, new CC().growX());
        box.setBackground(data.kind().background().get());
        return box;
    }

    private void addToolActivity(List<AgentResult.ToolActivity> activities) {
        if (!LlmSettings.INSTANCE.getShowToolActivity() || activities.isEmpty()) {
            return;
        }
        for (var activity : activities) {
            var label = new JLabel("<html><i>" + escapeHtml(activity.name() + "("
                + activity.arguments() + ")") + "</i></html>");
            label.setToolTipText(activity.result());
            var box = new JPanel(new MigLayout(new LC().insets("3 10 3 10")));
            box.setBorder(BorderFactory.createLineBorder(Color.LIGHT_GRAY));
            box.add(label);
            pOutput.add(box, new CC().growX());
        }
        scrollToEnd();
    }

    private static String escapeHtml(String s) {
        return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;");
    }

    /** Dispatches the outcome of the agent loop; must run on the EDT. */
    private void renderAgentResult(AgentResult result) {
        switch (result) {
            case AgentResult.Done done -> {
                addToolActivity(done.activities());
                addOutput(done.content());
            }
            case AgentResult.NeedsInput needsInput -> addQuestionBox(needsInput.question());
            case AgentResult.NeedsApproval needsApproval ->
                addApprovalBox(needsApproval.toolCall());
            case AgentResult.Failed failed -> {
                LOGGER.error("Agent turn failed", failed.error());
                addError(failed.error() == null ? "Unknown error"
                        : String.valueOf(failed.error().getMessage()));
            }
        }
        scrollToEnd();
    }

    private void addQuestionBox(AgentResult.Question question) {
        pOutput.add(new AskUserBox(question, this), new CC().growX());
        scrollToEnd();
    }

    private void addApprovalBox(AgentResult.ToolCallInfo toolCall) {
        pOutput.add(new ApprovalBox(toolCall, this), new CC().growX());
        scrollToEnd();
    }

    private void scrollToEnd() {
        if (LlmSettings.INSTANCE.getAutoScrollOutput()) {
            SwingUtilities.invokeLater(() -> scrpOutput.getVerticalScrollBar()
                    .setValue(scrpOutput.getVerticalScrollBar().getMaximum()));
        }
    }

    // ----------------------------------------------------------------- turn management

    private void beginTurn(String text) {
        if (running) {
            addError("An agent turn is already running; stop it first.");
            return;
        }
        if (text.isBlank()) {
            return;
        }
        var proof = mediator.getSelectedProof();
        var node = mediator.getSelectedNode();
        var session = LlmUtils.getSession(proof);

        // Pure /skills and /prompts messages are answered locally: the listing is rendered in the
        // chat without involving the LLM, so the command also works without a configured model.
        if (PromptResolver.isPureLibraryDirective(text)) {
            addInput(text);
            txtInput.setText("");
            var resolver = new PromptResolver.Context() {
                @Override
                public @Nullable Proof proof() {
                    return proof;
                }

                @Override
                public @Nullable Node node() {
                    return node;
                }
            };
            addOutput(PromptResolver.resolve(text, session, resolver).text());
            return;
        }

        var skillName = activeSkillOfCurrentSession();
        var skill = skillName == null ? null : SkillLibrary.INSTANCE.get(skillName);

        addInput(text);
        txtInput.setText("");
        setRunning(true);
        final var loop = new AgentLoop(session, new DefaultChatCompletionsClient());
        activeLoop = loop;
        runOnBackground(() -> loop.begin(text, proof, node, skill));
    }

    void answerQuestion(String answer) {
        final var loop = activeLoop;
        if (loop == null || running) {
            return;
        }
        setRunning(true);
        runOnBackground(() -> loop.answerQuestion(answer));
    }

    void decideApproval(boolean allow, boolean always) {
        final var loop = activeLoop;
        if (loop == null || running) {
            return;
        }
        setRunning(true);
        runOnBackground(() -> loop.decideApproval(allow, always));
    }

    void skipTurn() {
        if (activeLoop != null) {
            activeLoop.cancel();
        }
        setRunning(false);
    }

    private void runOnBackground(Supplier<AgentResult> action) {
        var thread = new Thread(() -> {
            AgentResult result;
            try {
                result = action.get();
            } catch (Exception e) {
                result = new AgentResult.Failed(e);
            }
            final var r = result;
            SwingUtilities.invokeLater(() -> {
                setRunning(false);
                renderAgentResult(r);
            });
        }, "keey-agent-loop");
        thread.setDaemon(true);
        thread.start();
    }

    private void setRunning(boolean value) {
        running = value;
        btnStop.setEnabled(value);
        btnStop.setToolTipText(value ? "Stop the running agent turn" : null);
    }

    // ------------------------------------------------------------------ TabPanel / actions

    @Override
    public @NonNull String getTitle() {
        return "KeY-Agent";
    }

    @Override
    public @NonNull JComponent getComponent() {
        return this;
    }

    @Override
    public @NonNull Collection<CAction> getTitleCActions() {
        Supplier<CMenu> supplier = () -> {
            CMenu menu = new CMenu();
            menu.add(actionSwitchOrientation.toCAction());

            CMenu menuModels = new CMenu("Models", null);
            menu.add(menuModels);
            var groupModels = new CRadioGroup();
            var llmSession = LlmUtils.getSession(mediator.getSelectedProof());

            for (var m : LlmSettings.INSTANCE.getAvailableModels()) {
                var selected = m.equals(llmSession.getModel());
                final var action = new CRadioButton(m, null) {
                    @Override
                    protected void changed() {
                        llmSession.setModel(m);
                    }
                };
                action.setSelected(selected);
                groupModels.add(action);
                menuModels.add(action);
            }
            return menu;
        };

        var a = new DynamicCMenu("Settings", IconFactory.properties(MainWindow.TOOLBAR_ICON_SIZE),
            supplier);
        var help = HelpFacade.createHelpButton("user/LLM/");
        return List.of(help, a);
    }

    class SwitchOrientationAction extends KeyAction {
        public SwitchOrientationAction() {
            setName("Switch Orientation");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (splitPane.getOrientation() == JSplitPane.HORIZONTAL_SPLIT) {
                splitPane.setOrientation(JSplitPane.VERTICAL_SPLIT);
            } else {
                splitPane.setOrientation(JSplitPane.HORIZONTAL_SPLIT);
            }
        }
    }

    class SendPromptAction extends KeyAction {
        public SendPromptAction() {
            setName("Send");
            putValue(SHORT_DESCRIPTION, "Send the prompt (Ctrl+Enter)");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            beginTurn(txtInput.getText());
        }
    }

    class ClearHistoryAction extends KeyAction {
        public ClearHistoryAction() {
            setName("Clear history");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            LlmUtils.getSession(mediator.getSelectedProof()).getContext().clear();
            pOutput.removeAll();
            pOutput.invalidate();
            pOutput.repaint();
        }
    }

    class PromptsMenuAction extends KeyAction {
        public PromptsMenuAction() {
            setName("Prompts");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            var menu = new JPopupMenu();
            for (var prompt : PromptLibrary.INSTANCE.all()) {
                var item = new JMenuItem(prompt.name());
                item.setToolTipText(prompt.description());
                item.addActionListener(ev -> txtInput.replaceSelection(
                    (txtInput.getCaretPosition() > 0
                            && !txtInput.getText().substring(0, txtInput.getCaretPosition())
                                    .endsWith(" ") ? " " : "")
                            + prompt.template()));
                menu.add(item);
            }
            menu.addSeparator();
            var newItem = new JMenuItem("+ new prompt\u2026");
            newItem.addActionListener(ev -> openLibrarySettings());
            menu.add(newItem);
            menu.show(LlmPrompt.this, 0, 30);
        }
    }

    static class CheckBoxFileAction extends KeyAction {
        private final Set<URI> selectedFiles;
        private final URI file;

        public CheckBoxFileAction(URI file, Set<URI> selectedFiles) {
            this.file = file;
            this.selectedFiles = selectedFiles;
            setName(file.toString());
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            var chk = (JCheckBox) e.getSource();
            if (chk.isSelected()) {
                selectedFiles.add(file);
            } else {
                selectedFiles.remove(file);
            }
        }
    }

    private class RepromptAction extends KeyAction {
        private final String prompt;

        public RepromptAction(String prompt) {
            this.prompt = prompt;
            setName("into input");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            txtInput.setText(prompt);
        }
    }
}


/**
 * A rendered message box in the conversation (input, answer or error). Right-click offers the
 * registered context actions (e.g. "into input").
 */
class OutputBox<T> extends JPanel {
    protected final LlmPromptModel<T> model;
    protected final JTextArea output = new JTextArea();
    protected final JPopupMenu menu = new JPopupMenu();

    public OutputBox(LlmPromptModel<T> userData) {
        this.model = userData;
        setLayout(new BorderLayout());
        output.setEditable(false);
        output.setText(userData.text());
        output.setLineWrap(true);
        output.setWrapStyleWord(true);
        output.setComponentPopupMenu(menu);
        setBorder(BorderFactory.createEmptyBorder(6, 10, 6, 10));
        add(new JScrollPane(output), BorderLayout.CENTER);
    }

    @Override
    public void setBackground(Color bg) {
        super.setBackground(bg);
        if (output != null) {
            output.setBackground(bg);
        }
    }
}


/**
 * Renders a question asked by the agent via {@code ask_user}. Answers are relayed to the running
 * {@link AgentLoop}, which continues the turn.
 */
class AskUserBox extends JPanel {
    public AskUserBox(AgentResult.Question question, LlmPrompt panel) {
        setLayout(new BorderLayout(8, 8));
        setBorder(BorderFactory.createCompoundBorder(BorderFactory.createLineBorder(Color.GRAY),
            BorderFactory.createEmptyBorder(8, 10, 8, 10)));
        setBackground(LlmPrompt.COLOR_BG_ACTION.get());
        var label = new JLabel("<html><b>Question:</b> " + text(question.text()) + "</html>");
        label.setBorder(BorderFactory.createEmptyBorder(0, 0, 6, 0));
        add(label, BorderLayout.NORTH);

        var options = question.options() == null ? List.<String>of() : question.options();
        if (options.isEmpty()) {
            var field = new JTextField(40);
            var go = new JButton("Send");
            var skip = new JButton("Skip");
            go.addActionListener(
                e -> panel.answerQuestion(field.getText()));
            skip.addActionListener(e -> panel.skipTurn());
            var row = new JPanel(new BorderLayout(4, 0));
            row.add(field, BorderLayout.CENTER);
            var buttons = new JPanel();
            buttons.add(go);
            buttons.add(skip);
            row.add(buttons, BorderLayout.EAST);
            field.addActionListener(e -> go.doClick());
            add(row, BorderLayout.CENTER);
        } else {
            var buttons = new JPanel(new java.awt.FlowLayout(
                java.awt.FlowLayout.LEFT, 6, 0));
            for (String option : options) {
                var b = new JButton(option);
                b.addActionListener(e -> panel.answerQuestion(option));
                buttons.add(b);
            }
            var skip = new JButton("Skip");
            skip.addActionListener(e -> panel.skipTurn());
            buttons.add(skip);
            add(buttons, BorderLayout.CENTER);
        }
    }

    private static String text(String s) {
        return s == null ? "" : s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;");
    }
}


/**
 * Renders a tool call that awaits user approval. The user may allow it once, allow it always
 * (remembered in the settings) or deny it.
 */
class ApprovalBox extends JPanel {
    public ApprovalBox(AgentResult.ToolCallInfo toolCall, LlmPrompt panel) {
        setLayout(new BorderLayout(8, 8));
        setBorder(BorderFactory.createCompoundBorder(BorderFactory.createLineBorder(Color.GRAY),
            BorderFactory.createEmptyBorder(8, 10, 8, 10)));
        setBackground(LlmPrompt.COLOR_BG_ACTION.get());
        var label = new JLabel("<html><b>Approval required:</b> " + "tool <code>"
            + text(toolCall.name()) + "</code><br/><code>" + text(toolCall.arguments())
            + "</code></html>");
        label.setBorder(BorderFactory.createEmptyBorder(0, 0, 6, 0));
        add(label, BorderLayout.NORTH);

        var buttons = new JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT, 6, 0));
        var allowOnce = new JButton("Allow once");
        allowOnce.addActionListener(e -> panel.decideApproval(true, false));
        buttons.add(allowOnce);
        var always = new JButton("Always allow");
        always.setToolTipText("Remember the decision for this tool (persisted in the settings)");
        always.addActionListener(e -> panel.decideApproval(true, true));
        buttons.add(always);
        var deny = new JButton("Deny");
        deny.addActionListener(e -> panel.decideApproval(false, false));
        buttons.add(deny);
        add(buttons, BorderLayout.SOUTH);
    }

    private static String text(String s) {
        return s == null ? "" : s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;");
    }
}
