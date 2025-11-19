package org.key_project.key.llm;

import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CMenu;
import bibliothek.gui.dock.common.action.CRadioButton;
import bibliothek.gui.dock.common.action.CRadioGroup;
import com.google.gson.GsonBuilder;
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
import de.uka.ilkd.key.proof.Proof;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import javax.swing.table.DefaultTableModel;
import java.awt.*;
import java.awt.event.*;
import java.io.IOException;
import java.net.URI;
import java.util.*;
import java.util.List;
import java.util.concurrent.ForkJoinPool;
import java.util.function.Supplier;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmPrompt extends JPanel implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(LlmPrompt.class);
    public static final ColorSettings.ColorProperty COLOR_BG_INPUT = ColorSettings.define(
            "llm.output.bg.input",
            "Background color in chat of LLM answers", new Color(130, 180, 220, 255));

    public static final ColorSettings.ColorProperty COLOR_BG_ERROR
            = ColorSettings.define("llm.output.bg.error", "Background color in chat of LLM answers", new Color(255, 180, 180, 255));

    public static final ColorSettings.ColorProperty COLOR_BG_ANSWER
            = ColorSettings.define("llm.output.bg.answer", "Background color in chat of LLM answers", Color.LIGHT_GRAY);

    private final JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);

    private final JEditorPane txtInput = new JEditorPane();

    private final JPanel pOutput = new JPanel(new MigLayout(new LC().fillX().debug().topToBottom().wrapAfter(1)));

    private final KeyAction actionSwitchOrientation = new SwitchOrientationAction();
    private final SendPromptAction actionSendPrompt = new SendPromptAction();
    private final JPanel tblFiles = new JPanel(new MigLayout(new LC().fillX().wrapAfter(1)));
    private final DefaultTableModel modelFiles = new DefaultTableModel();

    private final DefaultListModel<LlmPromptModel<?>> model = new DefaultListModel<>();
    private final MainWindow mainWindow;
    private final KeYMediator mediator;

    public LlmPrompt(MainWindow mainWindow, @NonNull KeYMediator mediator) {
        this.mainWindow = mainWindow;
        this.mediator = mediator;

        setLayout(new BorderLayout());
        add(splitPane, BorderLayout.CENTER);
        final var comp = new JScrollPane(pOutput);
        comp.getVerticalScrollBar().setUnitIncrement(16);
        splitPane.add(comp);
        var scrpInput = new JScrollPane(txtInput);
        var scrpFiles = new JScrollPane(tblFiles);
        var tabInputPanes = new JTabbedPane();
        tabInputPanes.addTab("Prompt", scrpInput);
        tabInputPanes.addTab("Files", scrpFiles);
        splitPane.add(tabInputPanes);

        SwingUtilities.invokeLater(this::populateFiles);
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                populateFiles();
            }
        });


        handle(new Exception("Test Exception"));
        handle(new GsonBuilder().create().fromJson("{\"id\":\"chatcmpl-CdLvyHhYLoKFk3F28rE6JgNJVGZHU\",\"created\":1763495142,\"model\":\"gpt-4.1-mini-2025-04-14\",\"object\":\"chat.completion\",\"system_fingerprint\":\"fp_3dcd5944f5\",\"choices\":[{\"finish_reason\":\"stop\",\"index\":0,\"message\":{\"content\":\"Die Rayleigh-Streuung beschreibt die Streuung von Licht an kleinen Teilchen, deren Größe viel kleiner ist als die Lichtwellenlänge. Dabei wird kurzwelliges Licht (blaues und violettes) stärker gestreut als langwelliges (rotes), was z.B. den blauen Himmel erklärt. Die Intensität der Streuung ist proportional zur vierten Potenz der Frequenz des Lichts.\",\"role\":\"assistant\",\"annotations\":[]},\"provider_specific_fields\":{\"content_filter_results\":{\"hate\":{\"filtered\":false,\"severity\":\"safe\"},\"protected_material_text\":{\"filtered\":false,\"detected\":false},\"self_harm\":{\"filtered\":false,\"severity\":\"safe\"},\"sexual\":{\"filtered\":false,\"severity\":\"safe\"},\"violence\":{\"filtered\":false,\"severity\":\"safe\"}}}}],\"usage\":{\"completion_tokens\":91,\"prompt_tokens\":36,\"total_tokens\":127,\"completion_tokens_details\":{\"accepted_prediction_tokens\":0,\"audio_tokens\":0,\"reasoning_tokens\":0,\"rejected_prediction_tokens\":0},\"prompt_tokens_details\":{\"audio_tokens\":0,\"cached_tokens\":0}},\"prompt_filter_results\":[{\"prompt_index\":0,\"content_filter_results\":{\"hate\":{\"filtered\":false,\"severity\":\"safe\"},\"jailbreak\":{\"filtered\":false,\"detected\":false},\"self_harm\":{\"filtered\":false,\"severity\":\"safe\"},\"sexual\":{\"filtered\":false,\"severity\":\"safe\"},\"violence\":{\"filtered\":false,\"severity\":\"safe\"}}}]}",
                Map.class));
        addInput("Input data");

        txtInput.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                if (e.getKeyChar() == KeyEvent.VK_ENTER && (e.getModifiersEx() & InputEvent.CTRL_DOWN_MASK) > 0) {
                    actionSendPrompt.run();
                }
            }
        });
    }

    static class AddFileAction extends KeyAction {
        private final Set<URI> selectedFiles;
        private final URI file;

        public AddFileAction(URI file, Set<URI> selectedFiles) {
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

    private void populateFiles() {
        try {
            tblFiles.removeAll();
            LlmSession session = LlmUtils.getSession(mediator.getSelectedProof());
            List<URI> possibleFiles = new ArrayList<>(LlmUtils.getPossibleFiles(mediator.getSelectedProof()));
            Set<URI> selectedFiles = session.getSelectedFiles();
            possibleFiles.sort(Comparator.comparing(URI::toString));
            for (URI file : possibleFiles) {
                tblFiles.add(new JCheckBox(new AddFileAction(file, selectedFiles)));
            }
            tblFiles.invalidate();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private OutputBox<String> addInput(String text) {
        var o = addBox(new LlmPromptModel(LlmPromptModel.Kind.INPUT, text, text), new RepromptAction(text));
        o.setBackground(COLOR_BG_INPUT.get());
        return o;
    }

    private <T> OutputBox<T> addBox(LlmPromptModel<T> data, Action... actions) {
        OutputBox<T> box = new OutputBox<>(data);
        for (Action it : actions) {
            box.menu.add(it);
        }
        pOutput.add(box, new CC().growX());
        box.setBackground(data.kind().background().get());
        return box;
    }

    private void handle(Map<String, Object> jsonResponse) {
        LOGGER.info("LLM prompt {}", jsonResponse);
        final var text = ((Map<String, Object>) ((Map<String, Object>) ((List<?>)
                jsonResponse.get("choices")).get(0)).get("message")).get("content").toString();
        addBox(new LlmPromptModel<>(LlmPromptModel.Kind.OUTPUT, text, jsonResponse));
    }

    private void handle(Throwable e) {
        addBox(new LlmPromptModel<>(LlmPromptModel.Kind.ERROR, e.toString(), e));
    }

    @Override
    public @NonNull String getTitle() {
        return "KiKI 2.0";
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
            var llmSession = LlmUtils.getSession(MainWindow.getInstance().getMediator().getSelectedProof());

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

        var a = new DynamicCMenu("Settings", IconFactory.properties(MainWindow.TOOLBAR_ICON_SIZE), supplier);
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

    static class SelectContextAction extends KeyAction {
        @Override
        public void actionPerformed(ActionEvent e) {

        }
    }

    class SendPromptAction extends KeyAction {
        public SendPromptAction() {
            setName("Send Prompt");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            run();
        }

        public void run() {
            var proof = MainWindow.getInstance().getMediator().getSelectedProof();
            var node = MainWindow.getInstance().getMediator().getSelectedNode();

            LlmSession session = LlmUtils.getSession(proof);
            var txt = txtInput.getText();
            LlmClient client = new LlmClient(session, new LlmContext(), txt);
            addInput(txt);
            txtInput.setText("");

            var sw = new SwingWorker<Map<String, Object>, Void>() {
                @Override
                protected Map<String, Object> doInBackground() throws Exception {
                    return client.call();
                }

                @Override
                protected void done() {
                    try {
                        handle(resultNow());
                    } catch (IllegalStateException ex) {
                        LOGGER.error("Exceptional case", exceptionNow());
                        handle(exceptionNow());
                    }
                }
            };
            ForkJoinPool.commonPool().submit(sw);
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

class OutputBox<T> extends JPanel {
    protected final LlmPromptModel<T> model;
    protected final JTextArea output = new JTextArea();
    protected final JPanel buttons = new JPanel();
    protected final JPopupMenu menu = new JPopupMenu();

    public OutputBox(LlmPromptModel<T> userData) {
        this.model = userData;
        setLayout(new BorderLayout());
        output.setEditable(false);
        add(output, 0);
        buttons.setVisible(false);
        output.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseEntered(MouseEvent e) {
                buttons.setVisible(true);
            }

            @Override
            public void mouseExited(MouseEvent e) {
                buttons.setVisible(false);
            }
        });
        output.setText(userData.text());
        output.setLineWrap(true); //Makes the text wrap to the next line
        output.setWrapStyleWord(true); //Makes the text wrap full words, not just letters
        output.setComponentPopupMenu(menu);
        setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
    }

    @Override
    public void setBackground(Color bg) {
        super.setBackground(bg);
        if (output != null) output.setBackground(bg);
    }
}
