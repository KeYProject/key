package org.key_project.key.cli;

public class Ansi {
    public static final char ESC = (char) 27;
    public static final int RED = 31;
    public static final int GREEN = 32;
    public static final int YELLOW = 33;
    public static final int BLUE = 34;
    public static final int MAGENTA = 35;
    public static final int CYAN = 36;
    public static final int WHITE = 37;

    public static boolean useColor = true;
    public static int currentPrintLevel = 0;
    public static boolean verbose = false;

    public static String color(Object s, int fg, int bg) {
        return ESC + "[" + fg + "m" + ESC + "[" + (bg + 10) + "m" + s + ESC + "[0m";
    }

    public static String colorfg(Object s, int c) {
        return ESC + "[" + c + "m" + s + ESC + "[0m";
    }

    public static String colorbg(Object s, int c) {
        return ESC + "[" + (c + 10) + "m" + s + ESC + "[0m";
    }

    public static void printBlock(String message, Runnable f) {
        info(message);
        currentPrintLevel++;
        f.run();
        currentPrintLevel--;
    }

    public static void printm(String message, Integer fg, Integer bg) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < currentPrintLevel; i++) {
            sb.append("  ");
        }
        String m;
        if (useColor) {
            m = message;
        } else if (fg != null && bg != null) {
            m = color(message, fg, bg);
        } else if (fg != null) {
            m = colorfg(message, fg);
        } else if (bg != null) {
            m = colorbg(message, bg);
        } else {
            m = message;
        }
        sb.append(m);
        System.out.println(sb);
    }

    public static void printm(String message) {
        printm(message, null, null);
    }

    public static void err(String message) {
        printm("[ERR ] " + message, RED, null);
    }

    public static void fail(String message) {
        printm("[FAIL] " + message, WHITE, RED);
    }

    public static void warn(String message) {
        printm("[WARN] " + message, YELLOW, null);
    }

    public static void info(String message) {
        printm("[FINE] " + message, BLUE, null);
    }

    public static void fine(String message) {
        printm("[OK  ] " + message, GREEN, null);
    }

    public static void debug(String message) {
        if (verbose) {
            printm("[    ] " + message, GREEN, null);
        }
    }
}