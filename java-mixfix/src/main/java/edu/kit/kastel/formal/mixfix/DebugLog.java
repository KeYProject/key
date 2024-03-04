/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

import java.util.Arrays;
import java.util.Stack;

/**
 * The Class DebugLog is a class with only static functions which allows to
 * simply trace memory entries and leaving.
 *
 * It is not multi-thread-compatible.
 *
 * When used and switched on (see {@link #DEBUG}) the methods
 * {@link #enter(Object...)} and {@link #leave(Object)} allow to add trace
 * statements to your code. Together with arguments and return values method
 * entries and leavings will then be printed with indention to the standard
 * output.
 *
 * @author mattias ulbrich
 */
public class DebugLog {


    /**
     * The stack of method calls.
     */
    private static Stack<String> methodStack = new Stack<String>();

    /**
     * The master switch to turn on and off.
     */
    private static boolean DEBUG = true;

    /**
     * If enter and leave are unmatched, this fails. run this to check the
     * failure!
     */
    private static final boolean ENSURE_GOOD = true;

    /**
     * Enter a method.
     *
     * @param args
     *            the arguments to the method.
     */
    public static void enter(Object... args) {
        if (!DEBUG) {
            return;
        }

        Exception ex = new Exception();
        StackTraceElement ste = ex.getStackTrace()[1];
        String method = ste.getClassName() + "." + ste.getMethodName();
        indent();
        System.out.println("> " + method);
        indent();
        System.out.println("  " + Arrays.asList(args));
        methodStack.push(method);
    }

    /**
     * Leave a method.
     *
     * @param returned
     *            the returned value.
     */
    public static void leave(Object returned) {
        if (!DEBUG) {
            return;
        }

        String method = methodStack.pop();

        if (ENSURE_GOOD) {
            Exception ex = new Exception();
            StackTraceElement ste = ex.getStackTrace()[1];
            String methodExpected = ste.getClassName() + "." + ste.getMethodName();
            if(!method.equals(methodExpected)) {
                throw new Error("Entered " + method + " but left " + methodExpected);
            }
        }

        indent();
        System.out.println("< " + method);
        indent();
        System.out.println("  " + returned);
    }

    /**
     * Indentation by level
     */
    private static void indent() {
        for (int i = 0; i < methodStack.size(); i++) {
            System.out.print(" ");
        }
    }

}
