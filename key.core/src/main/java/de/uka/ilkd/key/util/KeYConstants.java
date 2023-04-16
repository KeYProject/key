package de.uka.ilkd.key.util;

public interface KeYConstants {
    String INTERNAL_VERSION = KeYResourceManager.getManager().getSHA1();

    String VERSION =
        KeYResourceManager.getManager().getVersion() + " (internal: " + INTERNAL_VERSION + ")";

    String COPYRIGHT = UnicodeHelper.COPYRIGHT + " Copyright 2001"
        + UnicodeHelper.ENDASH + "2021 " + "Karlsruhe Institute of Technology, "
        + "Chalmers University of Technology, and Technische Universit\u00e4t Darmstadt";
}
