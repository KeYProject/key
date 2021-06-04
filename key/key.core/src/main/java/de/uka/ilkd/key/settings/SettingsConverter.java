// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.settings;

import java.util.Properties;

public class SettingsConverter {
    private static String[][] encoding = {
            {"#", "#hash"}, // must be the first in the list.
            {"\n", "#newline"},
            {"\t", "#tab"},
            {"=", "#equals"},
            {"\\\"", "#qmark"},
            {"\\\\", "#backslash"},
            {",", "#comma"
            }};
    private static final String PREFIX = "#beg";
    private static final String POSTFIX = "#end";
    private static final String LIST_SEPARATOR = ",";

    public static String convert(String str, boolean encode) {
        String result = str;
        for (String[] strings : encoding) {
            result = result.replaceAll(strings[encode ? 1 : 0],
                    strings[encode ? 0 : 1]);
        }
        return result;
    }

    public static String encode(String str) {
        int i = str.indexOf(PREFIX);
        if(i==0) {
            str = str.substring(PREFIX.length());
        }else{
            throw new RuntimeException(String.format(
                    "Given string '%s' has not the right prefix ('%s').", str, PREFIX));
        }
        i = str.lastIndexOf(POSTFIX);
        str = str.substring(0, i);
        return convert(str, true);
    }

    public static String decode(String str) {
        return PREFIX + convert(str, false) + POSTFIX;
    }


    public static String read(Properties props, String key, String defaultVal) {
        String eth = props.getProperty(key);
        try {
            return eth == null ? defaultVal : encode(eth);
        } catch (Exception e) {
            return defaultVal;
        }
    }

    public static int read(Properties props, String key, int defaultVal) {
        String eth = props.getProperty(key);
        if (eth == null) {
            return defaultVal;
        }
        try {
            return Integer.parseInt(eth);
        } catch (NumberFormatException e) {
            return defaultVal;
        }

    }

    public static long read(Properties props, String key, long defaultVal) {
        String eth = props.getProperty(key);
        if (eth == null) {
            return defaultVal;
        }
        try {
            return Long.parseLong(eth);
        } catch (NumberFormatException e) {
            return defaultVal;
        }
    }

    public static boolean read(Properties props, String key, boolean defaultVal) {
        String eth = props.getProperty(key);
        if (eth == null) {
            return defaultVal;
        }
        if (eth.equals("true")) {
            return true;
        }
        if (eth.equals("false")) {
            return false;
        }
        return defaultVal;
    }


    public static String[] read(Properties props, String key, String[] defaultVal) {

        String val = props.getProperty(key);
        if (val == null) {
            return defaultVal;
        }
        String[] result = val.split(LIST_SEPARATOR);
        for (int i = 0; i < result.length; i++) {
            try {
                result[i] = encode(result[i]);
            } catch (Exception e) {
                return defaultVal;
            }
        }
        return result;

    }


    public static void store(Properties props, String key, String[] values) {
        StringBuilder result = new StringBuilder();
        for (int i = 0; i < values.length; i++) {
            result.append(decode(values[i]));
            result.append(i < values.length - 1 ? "," : "");
        }
        props.setProperty(key, result.toString());
    }


    public static void store(Properties props, String key, String value) {
        if (key != null && value != null) {
            props.setProperty(key, decode(value));
        }
    }

    public static void store(Properties props, String key, boolean value) {
        if (key != null) {
            props.setProperty(key, value ? "true" : "false");
        }
    }

    public static void store(Properties props, String key, long value) {
        if (key != null) {
            props.setProperty(key, Long.toString(value));
        }
    }

    private SettingsConverter() {
    }
}