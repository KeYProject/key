package de.uka.ilkd.key.gui.settings;

import java.awt.*;
import java.util.HashMap;
import java.util.Map;
import javax.swing.*;

/**
 * @author Alexander Weigl
 * @version 1 (10.05.19)
 */
public class FontSizeFacade {
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
    private static final Map<String, Integer> originalFontSize = new HashMap<>();
    private static double currentFactor = 1;

    public static void saveCurrentFontSizes() {
        for (String k : KEYS) {
            Font f = UIManager.getDefaults().getFont(k);
            if (f != null) {
                originalFontSize.put(k, f.getSize());
            }
        }
    }

    /**
     * @param factor
     * @see SwingUtilities#updateComponentTreeUI(Component)
     */
    public static void resizeFonts(double factor) {
        if (Math.abs(currentFactor - factor) <= 0.1) {
            return;
        }

        currentFactor = factor;

        if (originalFontSize.isEmpty()) {
            saveCurrentFontSizes();
        }

        originalFontSize.forEach((key, value) -> {
            Font f = UIManager.getDefaults().getFont(key);
            if (f != null) {
                UIManager.getDefaults().put(key, f.deriveFont((float) (value * factor)));
            }
        });

        // redraw all frames
        for (Window w : Window.getWindows()) {
            SwingUtilities.updateComponentTreeUI(w);
        }

        for (Window w : Dialog.getWindows()) {
            SwingUtilities.updateComponentTreeUI(w);
        }

    }
}
