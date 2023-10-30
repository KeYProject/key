/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.Properties;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Proof-dependent settings for {@link TermLabel}s.
 *
 * @author lanzinger
 */
public class TermLabelSettings extends AbstractSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(TermLabelSettings.class);

    /**
     * Property key for {@link #getUseOriginLabels()}
     */
    public static final String USE_ORIGIN_LABELS = "[Labels]UseOriginLabels";

    /**
     * @see {@link #getUseOriginLabels()}
     */
    private boolean useOriginLabels = true;

    @Override
    public void readSettings(Properties props) {
        String str = props.getProperty(USE_ORIGIN_LABELS);

        if (str != null && (str.equals("true") || str.equals("false"))) {
            setUseOriginLabels(Boolean.parseBoolean(str));
        } else {
            setUseOriginLabels(true);
        }
    }

    @Override
    public void writeSettings(Properties props) {
        props.setProperty(USE_ORIGIN_LABELS, Boolean.toString(useOriginLabels));
    }

    /**
     *
     * @return {@code true} iff {@link OriginTermLabel}s should be used.
     */
    public boolean getUseOriginLabels() {
        return useOriginLabels;
    }

    /**
     * Sets the value returned by {@link #getUseOriginLabels()}
     *
     * @param useOriginLabels whether {@link OriginTermLabel}s should be used.
     */
    public void setUseOriginLabels(boolean useOriginLabels) {
        var old = this.useOriginLabels;
        this.useOriginLabels = useOriginLabels;
        firePropertyChange(USE_ORIGIN_LABELS, old, useOriginLabels);
    }
}
