package org.key_project.util;

import org.key_project.util.java.StringUtil;

/**
 * Helper functions for {@link String}s
 *
 * @author Alexander Weigl
 * @version 1 (29.03.19)
 */
public class Strings {
    /**
     * @deprecated This class has been merged with {@link org.key_project.util.java.StringUtil}.
     *             Call
     *             {@link org.key_project.util.java.StringUtil#containsWholeWord(String, String)}
     */
    @Deprecated
    public static boolean containsWholeWord(String s, String word) {
        return StringUtil.containsWholeWord(s, word);
    }

    /**
     * @deprecated This class has been merged with {@link org.key_project.util.java.StringUtil}.
     *             Call {@link org.key_project.util.java.StringUtil#isJMLComment(String)}
     */
    @Deprecated
    public static boolean isJMLComment(String comment) {
        return StringUtil.isJMLComment(comment);
    }
}
