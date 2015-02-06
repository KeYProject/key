package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.SemicolonClosedKeywordParser;

/**
 * Parses the content after a keyword which requires a storage location (or
 * storage locations) as content, e.g. the assignable keyword.
 *
 * @author Moritz Lichter
 *
 */
public class StoreRefKeywordContentParser extends
      SemicolonClosedKeywordParser {

   /**
    * Stores whether informal descriptions are allowed as storage locations.
    */
   private final boolean allowInformalDescription;

   /**
    * Crates a new {@link StoreRefKeywordContentParser}.
    *
    * @param allowInformalDescription
    *           whether the parser allows informal description
    */
   public StoreRefKeywordContentParser(final boolean allowInformalDescription) {
      super();
      this.allowInformalDescription = allowInformalDescription;
   }

   @Override
   protected ParseFunction createContentParseFunction(final IJMLProfile profile) {
      return new StoreRefListParser(profile, this.allowInformalDescription);
   }

}
