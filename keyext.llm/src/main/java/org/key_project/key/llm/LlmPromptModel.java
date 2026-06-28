package org.key_project.key.llm;

import de.uka.ilkd.key.gui.colors.ColorSettings;

import java.awt.*;

/**
 *
 * @author Alexander Weigl
 * @version 1 (28.06.26)
 */
public record LlmPromptModel<T>(Kind kind, String text, T data) {
    public enum Kind {
        INPUT(LlmPrompt.COLOR_BG_INPUT),
        OUTPUT(LlmPrompt.COLOR_BG_ANSWER),
        ERROR(LlmPrompt.COLOR_BG_ERROR);

        private final ColorSettings.ColorProperty bgColor;

        Kind(ColorSettings.ColorProperty bgColor) {
            this.bgColor = bgColor;
        }

        public ColorSettings.ColorProperty background() {
            return bgColor;
        }
    }

    @Override
    public String toString() {
        return text;
    }
}
