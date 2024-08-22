package org.key_project.rusty.ast;

import org.key_project.rusty.logic.ProgramPrefix;

public class ProgramPrefixUtil {

    public static class ProgramPrefixInfo {
        private final int length;

        public ProgramPrefixInfo(int length) {
            this.length = length;
        }

        public int getLength() {
            return length;
        }
    }

    public static ProgramPrefixInfo computeEssentials(ProgramPrefix prefix) {
        int length = 1;
        while (prefix.hasNextPrefixElement()) {
            prefix = prefix.getNextPrefixElement();
            length++;
        }
        return new ProgramPrefixUtil.ProgramPrefixInfo(length);
    }

}