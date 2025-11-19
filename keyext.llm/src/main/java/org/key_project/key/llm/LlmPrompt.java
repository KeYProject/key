package org.key_project.key.llm;

import com.google.gson.GsonBuilder;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ForkJoinPool;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmPrompt extends JPanel implements TabPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(LlmPrompt.class);
    private final JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);

    private final JEditorPane txtInput = new JEditorPane();

    private final Box pOutput = new Box(BoxLayout.Y_AXIS);

    private final KeyAction actionSwitchOrientation = new SwitchOrientationAction();

    public LlmPrompt() {
        setLayout(new BorderLayout());
        add(splitPane, BorderLayout.CENTER);
        splitPane.add(new JScrollPane(pOutput));
        splitPane.add(new JScrollPane(txtInput));

        handle(new Exception("Test Exception"));
        handle(new GsonBuilder().create().fromJson("{\"id\":\"chatcmpl-CdLvyHhYLoKFk3F28rE6JgNJVGZHU\",\"created\":1763495142,\"model\":\"gpt-4.1-mini-2025-04-14\",\"object\":\"chat.completion\",\"system_fingerprint\":\"fp_3dcd5944f5\",\"choices\":[{\"finish_reason\":\"stop\",\"index\":0,\"message\":{\"content\":\"Die Rayleigh-Streuung beschreibt die Streuung von Licht an kleinen Teilchen, deren Größe viel kleiner ist als die Lichtwellenlänge. Dabei wird kurzwelliges Licht (blaues und violettes) stärker gestreut als langwelliges (rotes), was z.B. den blauen Himmel erklärt. Die Intensität der Streuung ist proportional zur vierten Potenz der Frequenz des Lichts.\",\"role\":\"assistant\",\"annotations\":[]},\"provider_specific_fields\":{\"content_filter_results\":{\"hate\":{\"filtered\":false,\"severity\":\"safe\"},\"protected_material_text\":{\"filtered\":false,\"detected\":false},\"self_harm\":{\"filtered\":false,\"severity\":\"safe\"},\"sexual\":{\"filtered\":false,\"severity\":\"safe\"},\"violence\":{\"filtered\":false,\"severity\":\"safe\"}}}}],\"usage\":{\"completion_tokens\":91,\"prompt_tokens\":36,\"total_tokens\":127,\"completion_tokens_details\":{\"accepted_prediction_tokens\":0,\"audio_tokens\":0,\"reasoning_tokens\":0,\"rejected_prediction_tokens\":0},\"prompt_tokens_details\":{\"audio_tokens\":0,\"cached_tokens\":0}},\"prompt_filter_results\":[{\"prompt_index\":0,\"content_filter_results\":{\"hate\":{\"filtered\":false,\"severity\":\"safe\"},\"jailbreak\":{\"filtered\":false,\"detected\":false},\"self_harm\":{\"filtered\":false,\"severity\":\"safe\"},\"sexual\":{\"filtered\":false,\"severity\":\"safe\"},\"violence\":{\"filtered\":false,\"severity\":\"safe\"}}}]}",
                Map.class));
        addInput(">>> Input data");


        txtInput.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                if (e.getKeyChar() == KeyEvent.VK_ENTER && (e.getModifiersEx() & InputEvent.CTRL_DOWN_MASK) > 0) {
                    var proof = MainWindow.getInstance().getMediator().getSelectedProof();
                    var node = MainWindow.getInstance().getMediator().getSelectedNode();

                    LlmSession session = LlmUtils.getSession(proof);
                    LlmClient client = new LlmClient(session);

                    var txt = txtInput.getText();
                    addBox(txt);

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
                            } catch (Exception ex) {
                                LOGGER.error(ex.getMessage(), ex);
                                handle(ex);
                            }
                        }
                    };
                    ForkJoinPool.commonPool().submit(sw);
                }
            }
        });
    }

    public static class OutputBox<T> extends JPanel {
        private final T userData;
        private final JEditorPane output = new JEditorPane();
        private final JPanel buttons = new JPanel();
        private final JPopupMenu menu = new JPopupMenu();

        public OutputBox(T userData) {
            this(userData, userData.toString());
        }

        public OutputBox(T userData, String text) {
            this.userData = userData;
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
            output.setText(text);

            setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        }

        @Override
        public void setBackground(Color bg) {
            super.setBackground(bg);
            if (output != null) output.setBackground(bg);
        }
    }

    private OutputBox<String> addInput(String text) {
        var o= addBox(text, new RepromptAction(text));
        o.setBackground(new Color(130, 180, 220, 255));
        return o;
    }

    private <T> OutputBox<T> addBox(T data, Action... action) {
        OutputBox<T> box = new OutputBox<>(data);
        pOutput.add(box);
        return box;
    }

    private void handle(Map<String, Object> jsonResponse) {
        LOGGER.info("LLM prompt {}", jsonResponse);
        var o = new OutputBox<>(jsonResponse,
                ((Map<String, Object>) ((Map<String, Object>) ((List<?>) jsonResponse.get("choices")).get(0)).get("message")).get("content").toString());
        pOutput.add(o);
    }

    private void handle(Throwable e) {
        LOGGER.error("Error during LLM prompt", e);
        var box = addBox(e);
        box.setBackground(new Color(255, 180, 180, 255));
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
    public @NonNull Collection<Action> getTitleActions() {
        return List.of(actionSwitchOrientation);
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

    class SelectContextAction extends KeyAction {
        @Override
        public void actionPerformed(ActionEvent e) {

        }
    }

    class SendPromptAction extends KeyAction {
        @Override
        public void actionPerformed(ActionEvent e) {
            String prompt = txtInput.getText();
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
