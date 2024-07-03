/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.util;

public interface KeYConstants {
    public static final String INTERNAL_VERSION = KeYResourceManager.getManager().getSHA1();

    public static final String VERSION =
        KeYResourceManager.getManager().getVersion() + " (internal: " + INTERNAL_VERSION + ")";

    public static final String COPYRIGHT = UnicodeHelper.COPYRIGHT
        + " Copyright 2001"
        + UnicodeHelper.ENDASH
        + "2021 "
        + "Karlsruhe Institute of Technology, "
        + "Chalmers University of Technology, and Technische Universit\u00e4t Darmstadt";
}
