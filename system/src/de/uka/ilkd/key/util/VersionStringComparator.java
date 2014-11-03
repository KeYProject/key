package de.uka.ilkd.key.util;

import java.util.Comparator;

/**
 * Compares Strings by integer values of 'dot' separated components.
 * @author bruns
 *
 */
public class VersionStringComparator implements Comparator<String> {
    
    private final static String SEPARATOR_PATTERN = "\\D";

    private final LexicographicComparator<Integer> lxc = new LexicographicComparator<Integer>();

    @Override
    public int compare(String arg0, String arg1) {
        return lxc.compare(parseVersionString(arg0), parseVersionString(arg1));
    }

    private static Integer[] parseVersionString(String s) {
        final String[] p = s.split(SEPARATOR_PATTERN);
        final Integer[] r = new Integer[p.length];
        for (int i= 0; i < p.length; i++) {
            r[i] = parseInt(p[i]);
        }
        return r;
    }
    
    private static Integer parseInt(String s) {
        try {
            return Integer.parseInt(s);
        } catch (NumberFormatException e) {
            return Integer.valueOf(-1);
        }
    }
}
