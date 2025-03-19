/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.awt.*;
import java.util.HashMap;
import java.util.Map;
import javax.swing.*;
import javax.swing.plaf.FontUIResource;


/**
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public final class FontSizeFacade {
    private static final String[] KEYS = new String[] { "Button.font", "CheckBox.font",
        "CheckBoxMenuItem.acceleratorFont", "CheckBoxMenuItem.font", "ColorChooser.font",
        "ComboBox.font", "EditorPane.font", "FormattedTextField.font", "IconButton.font",
        "InternalFrame.optionDialogTitleFont", "InternalFrame.paletteTitleFont",
        "InternalFrame.titleFont", "Label.font", "List.font", "Menu.acceleratorFont", "Menu.font",
        "MenuBar.font", "MenuItem.acceleratorFont", "MenuItem.font", "OptionPane.buttonFont",
        "OptionPane.font", "OptionPane.messageFont", "Panel.font", "PasswordField.font",
        "PopupMenu.font", "ProgressBar.font", "RadioButton.font",
        "RadioButtonMenuItem.acceleratorFont", "RadioButtonMenuItem.font", "ScrollPane.font",
        "Slider.font", "Spinner.font", "TabbedPane.font", "TabbedPane.smallFont", "Table.font",
        "TableHeader.font", "TextArea.font", "TextField.font", "TextPane.font", "TitledBorder.font",
        "ToggleButton.font", "ToolBar.font", "ToolTip.font", "Tree.font", "Viewport.font" };
    private static final Map<String, Float> ORIGINAL_FONT_SIZES = new HashMap<>();
    private static double currentFactor = 1;

    private FontSizeFacade() {
    }

    private static void saveCurrentFontSizes() {
        for (String k : KEYS) {
            Font f = UIManager.getFont(k);
            if (f != null) {
                ORIGINAL_FONT_SIZES.put(k, (float) f.getSize());
            }
        }
    }

    /**
     * Scale all managed fonts by the provided factor. Then attempts to redraw all components.
     *
     * @param factor the factor
     * @see SwingUtilities#updateComponentTreeUI(Component)
     */
    public static void resizeFonts(double factor) {
        if (Math.abs(currentFactor - factor) <= 0.1) {
            return;
        }

        currentFactor = factor;

        if (ORIGINAL_FONT_SIZES.isEmpty()) {
            saveCurrentFontSizes();
        }

        ORIGINAL_FONT_SIZES.forEach((key, value) -> {
            Font f = UIManager.getFont(key);
            // https://stackoverflow.com/a/6930659/5837178
            if (f instanceof FontUIResource) {
                UIManager.put(key,
                    new FontUIResource(f.getName(), f.getStyle(), (int) (value * factor)));
            } else if (f != null) {
                UIManager.put(key, f.deriveFont((float) (value * factor)));
            }
        });

        // redraw all frames and dialogs
        for (Window w : Window.getWindows()) {
            SwingUtilities.updateComponentTreeUI(w);
        }
    }
}
