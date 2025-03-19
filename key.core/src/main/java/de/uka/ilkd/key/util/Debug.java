/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * {@code Debug} offers some methods for assertions, debug output and so on.
 */
public final class Debug {
    private static final Logger LOGGER = LoggerFactory.getLogger(Debug.class);

    /**
     * has to be set in order to enable assertion
     */
    public static final boolean ENABLE_ASSERTION =
        Boolean.parseBoolean(System.getProperty("KeyAssertionFlag", "true"));

    /**
     * has to be set in order to enable debugging
     */
    public static boolean ENABLE_DEBUG = "on".equals(System.getProperty("KeyDebugFlag"))
            || "on".equals(System.getenv("KeyDebugFlag"));


    /**
     * an assertion failure is thrown if isOK is evaluated to false
     *
     * @param isOK boolean the assertion that is checked
     */
    public static void assertTrue(boolean isOK) {
        if (ENABLE_ASSERTION) {
            if (!isOK) {
                fail();
            }
        }
    }

    public static void assertFalse(boolean isNotOK) {
        assertTrue(!isNotOK);
    }

    /**
     * an assertion failure is thrown if isOK is evaluated to false the text in message is handed
     * over to this exception
     *
     * @param isOK boolean the assertion that is checked
     * @param message String describes the failed assertion
     */
    public static void assertTrue(boolean isOK, String message) {
        if (ENABLE_ASSERTION) {
            if (!isOK) {
                fail(message);
            }
        }
    }

    /**
     * an assertion failure is thrown if isOK is evaluated to false the text in message is handed
     * over to this exception
     *
     * @param isOK boolean the assertion that is checked
     * @param message String describes the failed assertion
     */
    public static void assertTrue(boolean isOK, String message, Object parameter) {
        if (ENABLE_ASSERTION) {
            if (!isOK) {
                fail(message + ":" + parameter);
            }
        }
    }

    /**
     * an assertion failure is thrown if an iterable object is either null or contains the null
     * element.
     *
     * @param iterable The iterable object to check
     * @param message String describes the failed assertion
     */
    public static void assertDeepNonNull(Iterable<?> iterable, String message) {
        if (ENABLE_ASSERTION) {
            if (iterable == null) {
                fail("Null pointer: " + message);
            }
            for (Object object : iterable) {
                if (object == null) {
                    fail("Null element in collection:" + message);
                }
            }
        }
    }

    public static void assertFalse(boolean isNotOK, String message) {
        assertTrue(!isNotOK, message);
    }

    public static void fail() {
        fail("No further information available.");
    }

    public static void fail(String message) {
        if (ENABLE_ASSERTION) {
            throw new AssertionFailure("\nAssertion failure: " + message);
        }
    }

    public static void fail(String message, Object o) {
        if (ENABLE_ASSERTION) {
            throw new AssertionFailure("\nAssertion failure: " + message + ":" + o);
        }
    }
}
