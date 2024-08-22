/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
