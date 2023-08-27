/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.fonticons;

import javax.swing.*;

public abstract class IconProvider {
    Icon load() {
        return load(16);
    }

    abstract Icon load(float height);

    abstract String getKey(float size);

    public Icon get() {
        return get(IconFactory.DEFAULT_SIZE);
    }

    public Icon get(float height) {
        return IconFactory.get(this, height);
    }
}
