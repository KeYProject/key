package de.uka.ilkd.key.util;

public interface KeYConstants {
   public static final String INTERNAL_VERSION = KeYResourceManager.getManager().getSHA1();

   public static final String VERSION = KeYResourceManager.getManager().getVersion() + " (internal: " + INTERNAL_VERSION + ")";

   public static final String COPYRIGHT = UnicodeHelper.COPYRIGHT
                                          + " Copyright 2001"
                                          + UnicodeHelper.ENDASH
                                          + "2015 "
                                          + "Karlsruhe Institute of Technology, "
                                          + "Chalmers University of Technology, and Technische Universit\u00e4t Darmstadt";
}
