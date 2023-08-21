/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.configuration;

import java.awt.Font;
import java.util.ArrayList;
import java.util.List;
import javax.swing.UIManager;
import javax.swing.plaf.FontUIResource;

import de.uka.ilkd.key.settings.ProofIndependentSettings;

/** this class is used to set some default gui properties */
public class Config {

    /** name of different fonts */
    public static final String KEY_FONT_PROOF_TREE = "KEY_FONT_PROOF_TREE";
    public static final String KEY_FONT_SEQUENT_VIEW = "KEY_FONT_CURRENT_GOAL_VIEW";
    public static final String KEY_FONT_GOAL_LIST_VIEW = "KEY_FONT_GOAL_LIST_VIEW";
    public static final String KEY_FONT_PROOF_LIST_VIEW = "KEY_FONT_PROOF_LIST_VIEW";

    /** An array of font sizes for the goal view */
    public static final int[] SIZES = new int[] { 10, 12, 14, 17, 20, 24 };

    public static final Config DEFAULT = new Config();

    /** The index of the current size */
    private int sizeIndex = readSizeIndex();
    private double sizeFactor = readSizeFactor();

    /** cached ConfigChange event */
    private final ConfigChangeEvent configChangeEvent = new ConfigChangeEvent(this);

    /** the listeners to this Config */
    private final List<ConfigChangeListener> listenerList = new ArrayList<>(5);

    private Config() {
        setDefaultFonts();
    }

    public void larger() {
        if (!isMaximumSize()) {
            sizeIndex++;
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setFontIndex(sizeIndex);
            // ProofSettings.DEFAULT_SETTINGS.getViewSettings().setFontIndex(sizeIndex);
            setDefaultFonts();
            fireConfigChange();
        }
    }

    public void smaller() {
        if (!isMinimumSize()) {
            sizeIndex--;
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setFontIndex(sizeIndex);
            // ProofSettings.DEFAULT_SETTINGS.getViewSettings().setFontIndex(sizeIndex);
            setDefaultFonts();
            fireConfigChange();
        }
    }

    public boolean isMinimumSize() {
        return sizeIndex == 0;
    }

    public boolean isMaximumSize() {
        return sizeIndex == SIZES.length - 1;
    }

    private int readSizeIndex() {
        int s = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().sizeIndex();
        if (s < 0 || s > SIZES.length) {
            s = 0;
        }
        return s;
    }

    private double readSizeFactor() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getUIFontSizeFactor();
    }

    public void setDefaultFonts() {
        sizeFactor = readSizeFactor();
        int idx = readSizeIndex();
        UIManager.put(KEY_FONT_PROOF_TREE,
            new FontUIResource("Default", Font.PLAIN, (int) (sizeFactor * SIZES[idx])));
        UIManager.put(KEY_FONT_SEQUENT_VIEW,
            new FontUIResource("Monospaced", Font.PLAIN, (int) (sizeFactor * SIZES[idx])));
        UIManager.put(KEY_FONT_GOAL_LIST_VIEW,
            new FontUIResource("Default", Font.PLAIN, (int) (sizeFactor * SIZES[2])));
        UIManager.put(KEY_FONT_PROOF_LIST_VIEW,
            new FontUIResource("Default", Font.PLAIN, (int) (sizeFactor * SIZES[2])));
    }


    public void addConfigChangeListener(ConfigChangeListener listener) {
        synchronized (listenerList) {
            listenerList.add(listener);
        }
    }

    public void removeConfigChangeListener(ConfigChangeListener listener) {
        synchronized (listenerList) {
            listenerList.remove(listener);
        }
    }

    public synchronized void fireConfigChange() {
        synchronized (listenerList) {
            for (ConfigChangeListener aListenerList : listenerList) {
                aListenerList.configChanged(configChangeEvent);
            }
        }
    }

}
