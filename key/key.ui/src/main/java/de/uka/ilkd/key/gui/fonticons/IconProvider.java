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
