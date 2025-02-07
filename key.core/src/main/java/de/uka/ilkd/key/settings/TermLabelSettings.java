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

    public static final String USE_ORIGIN_LABELS = "UseOriginLabels";

    public static final String CATEGORY = "Labels";

    private boolean useOriginLabels = true;

    private void readSettings(Properties props) {
        String str = props.getProperty("[" + CATEGORY + "]" + USE_ORIGIN_LABELS);

        if (str != null && (str.equals("true") || str.equals("false"))) {
            setUseOriginLabels(Boolean.parseBoolean(str));
        } else {
            setUseOriginLabels(true);
        }
    }

    private void writeSettings(Properties props) {
        props.setProperty("[" + CATEGORY + "]" + USE_ORIGIN_LABELS,
            Boolean.toString(useOriginLabels));
    }

    @Override
    public void readSettings(Configuration props) {
        var category = props.getSection(CATEGORY);
        if (category == null)
            return;
        try {
            setUseOriginLabels(category.getBool(USE_ORIGIN_LABELS));
        } catch (Exception e) {
            LOGGER.debug("TermLabelSettings: Failure while reading the setting \"UseOriginLabels\"."
                + "Using the default value: true." + "The string read was: {}",
                category.get(USE_ORIGIN_LABELS), e);
            setUseOriginLabels(true);
        }
    }

    @Override
    public void writeSettings(Configuration props) {
        var category = props.getOrCreateSection(CATEGORY);
        category.set(USE_ORIGIN_LABELS, useOriginLabels);
    }

    /**
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
