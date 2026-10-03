/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.*;

import de.uka.ilkd.key.gui.colors.ColorSettings;

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
