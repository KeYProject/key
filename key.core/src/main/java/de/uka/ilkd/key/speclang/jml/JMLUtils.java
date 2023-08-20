/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import java.util.Set;
import java.util.TreeSet;
import javax.annotation.Nonnull;

@Deprecated
public abstract class JMLUtils {
    /**
     * The feature identifier for JML "feature switches" which will be (de-)activate JML comments
     * for KeY.
     */
    private static final String KEY_TOOL_IDENTIFIER = "key";

    /**
     * Split a given string of JML marker into the single markers. For example, "+key-esc" becomes
     * the the set with "+key" and "-esc". This method recognises the end of the marker by an
     * {@code @} sign or by the end of the string. It also is aware of potential comment starters,
     * i.e., "//" or "/*".
     */
    public static @Nonnull Set<String> splitJmlMarker(@Nonnull String starter) {
        Set<String> features = new TreeSet<>();
        int start = 0;
        if (starter.startsWith("//") || starter.startsWith("/*")) {
            start = 2;
        }
        int posAt = starter.indexOf('@');
        int end = posAt >= 0 ? posAt : starter.length();
        String[] markers = starter.substring(start, end).split("(?=[+-])");
        for (String marker : markers) {
            marker = marker.trim();
            if (!marker.isEmpty()) {
                features.add(marker.toLowerCase());
            }
        }
        return features;
    }

    /**
     * Decides whether the given string is a JML marker that symbolise a recognisable JML comment.
     * Refer to chapter 4.4. in the jml ref manual.
     * <p>
     * Uses {@link #KEY_TOOL_IDENTIFIER} as the marker for this KeY.
     */
    public static boolean isJmlCommentStarter(@Nonnull String starter) {
        return isJmlCommentStarter(starter, KEY_TOOL_IDENTIFIER);
    }

    /**
     * Decides whether the given string is a JML marker that symbolise a recognisable JML comment
     * for the given marker of the {@code tool}. Refer to chapter 4.4. in the jml ref manual.
     *
     * @param jmlMarkers the marker string at the beginning of an JML comment.
     * @param tool the marker of the current tool
     * @return true if the given jml markers represents a KeY-recognisable comment.
     */
    public static boolean isJmlCommentStarter(String jmlMarkers, String tool) {
        if (hasWhitespaceBeforeAt(jmlMarkers)) {
            return false;
        }

        tool = tool.toLowerCase(); // switches are in lower case
        Set<String> switches = splitJmlMarker(jmlMarkers);
        boolean containsPositive = switches.stream().anyMatch(it -> it.charAt(0) == '+');
        boolean allowsGivenTool = switches.contains("+" + tool);
        boolean forbidsGivenTool = switches.contains("-" + tool);
        boolean disabledCompletely = switches.contains("-") || switches.contains("+");
        boolean wrongMarkerFormat =
            switches.stream().anyMatch(it -> it.charAt(0) != '+' && it.charAt(0) != '-');

        if (disabledCompletely || forbidsGivenTool || wrongMarkerFormat) {
            return false;
        }

        // +OPENJML excludes KeY except KeY is enabled additionally with +key.
        return !containsPositive || allowsGivenTool;
    }

    private static boolean hasWhitespaceBeforeAt(String features) {
        int posAt = features.indexOf('@');
        int end = posAt >= 0 ? posAt : features.length();
        return features.substring(0, end).indexOf(' ') >= 0;
    }
}
