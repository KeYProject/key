/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.smt.lang;

public class Util {
    public static String processName(String id) {
        // is symbol already quoted?
        if (id.startsWith("|") && id.endsWith("|")) {
            return id;
        }


        // id = id.replace("store", "store_");
        id = id.replace("select", "select_");


        // do i need to quote symbol?
        boolean quote = id.contains(":") || id.contains(">") || id.contains("<") || id.contains("$")
                || id.contains("[") || id.contains("]");

        if (quote) {
            return "|" + id + "|";
        } else {
            return id;
        }
    }
}
