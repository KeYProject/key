/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import org.key_project.util.java.StringUtil;

public class Constants {
    /**
     * Constant for the line break which is used by the operating system.
     * <p>
     * <b>Do not use {@code \n}!</b>
     */
    public static final String NEW_LINE = StringUtil.NEW_LINE;
    public static final String NULLABLE = "/*@ nullable */";
    public static final String ALL_OBJECTS = "allObjects";
    public static final String ALL_INTS = "allInts";
    public static final String ALL_BOOLS = "allBools";
    public static final String ALL_HEAPS = "allHeaps";
    public static final String ALL_FIELDS = "allFields";
    public static final String ALL_SEQ = "allSeq";
    public static final String ALL_LOCSETS = "allLocSets";
    public static final String OBJENESIS_NAME = "objenesis-2.2.jar";
    public static final String OLD_MAP = "old";
    public static final String TAB = "   ";
    public static final String DUMMY_POSTFIX = "DummyImpl";

    private Constants() {
    }
}
