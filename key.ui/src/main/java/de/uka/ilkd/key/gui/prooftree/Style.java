/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.prooftree;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import javax.annotation.Nonnull;
import javax.swing.Icon;

import de.uka.ilkd.key.pp.LogicPrinter;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class Style {
    /** the text of this node */
    public String text;

    /** the tooltip */
    public Tooltip tooltip;

    /** foreground color of the node */
    public Color foreground;

    /** background color of the node */
    public Color background;

    /** border color of the node */
    public Color border;

    /** icon of the node */
    public Icon icon;

    /** Wrapper class for the tooltip */
    public static class Tooltip {
        /** title, can also be null and empty */
        private String title;

        /** infos */
        private final ArrayList<Fragment> additionalInfo = new ArrayList<>();

        /**
         * @return the title
         */
        public String getTitle() {
            return title;
        }

        /**
         * Sets the title.
         *
         * @param title tooltip title
         */
        public void setTitle(String title) {
            this.title = title;
        }

        /**
         * Adds a piece of additional information.
         *
         * @param key the key
         * @param value the value
         * @param block whether this should be rendered as a block
         */
        public void addAdditionalInfo(@Nonnull String key, @Nonnull String value, boolean block) {
            additionalInfo.add(new Fragment(key, value, block));
        }

        /**
         * Adds notes
         *
         * @param notes the notes
         */
        public void addNotes(@Nonnull String notes) {
            addAdditionalInfo("Notes", notes, false);
        }

        /**
         * Adds rule information
         *
         * @param rule the rule
         */
        public void addRule(@Nonnull String rule) {
            addAdditionalInfo("Rule", rule, false);
        }

        /**
         * Adds applied on infos
         *
         * @param on the info
         */
        public void addAppliedOn(@Nonnull String on) {
            addAdditionalInfo("Applied on", LogicPrinter.escapeHTML(on, true), true);
        }

        /**
         * @return list of all additional infos, immutable
         */
        public List<Fragment> getAdditionalInfos() {
            return Collections.unmodifiableList(additionalInfo);
        }

        /** wrapper class for additional infos */
        public static final class Fragment {
            /** key */
            public final String key;
            /** value */
            public final String value;
            /** whether this is a block */
            public final boolean block;

            public Fragment(String key, String value, boolean block) {
                this.key = key;
                this.value = value;
                this.block = block;
            }
        }
    }
}
