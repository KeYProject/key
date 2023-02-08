/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import java.io.IOException;

public interface IconFont {
    Font getFont() throws IOException, FontFormatException;

    char getUnicode();
}
