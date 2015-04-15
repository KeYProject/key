package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;

public final class LocSetSuffix {

   private LocSetSuffix() {

   }

   public static ParseFunction locSetSuffixes() {
      final ParseFunction arrayAll = seq(constant("["), constant("*"),
            constant("]"));
      final ParseFunction allFields = seq(constant("."), constant("*"));

      return alt(arrayAll, allFields);
   }

}
