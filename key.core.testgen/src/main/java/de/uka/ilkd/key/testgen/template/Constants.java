package de.uka.ilkd.key.testgen.template;

import org.key_project.util.java.StringUtil;

public interface Constants {

    /**
     * Constant for the line break which is used by the operating system.
     * <p>
     * <b>Do not use {@code \n}!</b>
     */
    String NEW_LINE = StringUtil.NEW_LINE;
    String NULLABLE = "/*@ nullable */";
    String ALL_OBJECTS = "allObjects";
    String ALL_INTS = "allInts";
    String ALL_BOOLS = "allBools";
    String ALL_HEAPS = "allHeaps";
    String ALL_FIELDS = "allFields";
    String ALL_SEQ = "allSeq";
    String ALL_LOCSETS = "allLocSets";

    String OBJENESIS_NAME = "objenesis-2.2.jar";

    String OLDMap = "old";

    String TAB = "   ";

    String DUMMY_POSTFIX = "DummyImpl";
}
