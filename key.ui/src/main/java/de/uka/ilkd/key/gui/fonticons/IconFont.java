package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import java.io.IOException;

public interface IconFont {
    Font getFont() throws IOException, FontFormatException;

    char getUnicode();
}
