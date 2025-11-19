package org.key_project.key.llm;

import com.google.gson.GsonBuilder;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.util.Arrays;
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
    public static final ColorSettings.ColorProperty COLOR_BG_INPUT = ColorSettings.define(
            "llm.output.bg.input",
            "Background color in chat of LLM answers", new Color(130, 180, 220, 255));

    public static final ColorSettings.ColorProperty COLOR_BG_ERROR
            = ColorSettings.define("llm.output.bg.error", "Background color in chat of LLM answers", new Color(255, 180, 180, 255));

    private static final ColorSettings.ColorProperty COLOR_BG_ANSWER
            = ColorSettings.define("llm.output.bg.answer", "Background color in chat of LLM answers", Color.LIGHT_GRAY);

    private final JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT);

    private final JEditorPane txtInput = new JEditorPane();

    private final JPanel pOutput = new JPanel(new MigLayout(new LC().fillX().debug().topToBottom().wrapAfter(1)));

    private final KeyAction actionSwitchOrientation = new SwitchOrientationAction();
    private final SendPromptAction actionSendPrompt = new SendPromptAction();

    public LlmPrompt() {
        setLayout(new BorderLayout());
        add(splitPane, BorderLayout.CENTER);
        final var comp = new JScrollPane(pOutput);
        comp.getVerticalScrollBar().setUnitIncrement(16);
        splitPane.add(comp);
        splitPane.add(new JScrollPane(txtInput));

        handle(new Exception("Test Exception"));
        handle(new GsonBuilder().create().fromJson("{\"id\":\"chatcmpl-CdLvyHhYLoKFk3F28rE6JgNJVGZHU\",\"created\":1763495142,\"model\":\"gpt-4.1-mini-2025-04-14\",\"object\":\"chat.completion\",\"system_fingerprint\":\"fp_3dcd5944f5\",\"choices\":[{\"finish_reason\":\"stop\",\"index\":0,\"message\":{\"content\":\"Die Rayleigh-Streuung beschreibt die Streuung von Licht an kleinen Teilchen, deren Größe viel kleiner ist als die Lichtwellenlänge. Dabei wird kurzwelliges Licht (blaues und violettes) stärker gestreut als langwelliges (rotes), was z.B. den blauen Himmel erklärt. Die Intensität der Streuung ist proportional zur vierten Potenz der Frequenz des Lichts.\",\"role\":\"assistant\",\"annotations\":[]},\"provider_specific_fields\":{\"content_filter_results\":{\"hate\":{\"filtered\":false,\"severity\":\"safe\"},\"protected_material_text\":{\"filtered\":false,\"detected\":false},\"self_harm\":{\"filtered\":false,\"severity\":\"safe\"},\"sexual\":{\"filtered\":false,\"severity\":\"safe\"},\"violence\":{\"filtered\":false,\"severity\":\"safe\"}}}}],\"usage\":{\"completion_tokens\":91,\"prompt_tokens\":36,\"total_tokens\":127,\"completion_tokens_details\":{\"accepted_prediction_tokens\":0,\"audio_tokens\":0,\"reasoning_tokens\":0,\"rejected_prediction_tokens\":0},\"prompt_tokens_details\":{\"audio_tokens\":0,\"cached_tokens\":0}},\"prompt_filter_results\":[{\"prompt_index\":0,\"content_filter_results\":{\"hate\":{\"filtered\":false,\"severity\":\"safe\"},\"jailbreak\":{\"filtered\":false,\"detected\":false},\"self_harm\":{\"filtered\":false,\"severity\":\"safe\"},\"sexual\":{\"filtered\":false,\"severity\":\"safe\"},\"violence\":{\"filtered\":false,\"severity\":\"safe\"}}}]}",
                Map.class));
        addInput(">>> Input data");


        txtInput.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                if (e.getKeyChar() == KeyEvent.VK_ENTER && (e.getModifiersEx() & InputEvent.CTRL_DOWN_MASK) > 0) {
                    actionSendPrompt.run();
                }
            }
        });
    }

    public static class OutputBox<T> extends JPanel {
        protected final T userData;
        protected final JEditorPane output = new JEditorPane();
        protected final JPanel buttons = new JPanel();
        protected final JPopupMenu menu = new JPopupMenu();

        public OutputBox(T userData) {
            this(userData, userData.toString());
            output.add(menu);
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
        var o = addBox(text, new RepromptAction(text));
        o.setBackground(COLOR_BG_INPUT.get());
        return o;
    }

    private <T> OutputBox<T> addBox(T data, Action... actions) {
        OutputBox<T> box = new OutputBox<>(data);
        for (Action it : actions) {
            box.menu.add(it);
        }
        pOutput.add(box, new CC().growX());
        return box;
    }

    private void handle(Map<String, Object> jsonResponse) {
        LOGGER.info("LLM prompt {}", jsonResponse);
        var o = new OutputBox<>(jsonResponse,
                ((Map<String, Object>) ((Map<String, Object>) ((List<?>) jsonResponse.get("choices")).get(0)).get("message")).get("content").toString());
        pOutput.add(o, new CC().growX());
        o.setBackground(COLOR_BG_ANSWER.get());
    }

    private void handle(Throwable e) {
        LOGGER.error("Error during LLM prompt", e);
        var box = addBox(e);
        box.setBackground(COLOR_BG_ERROR.get());
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
