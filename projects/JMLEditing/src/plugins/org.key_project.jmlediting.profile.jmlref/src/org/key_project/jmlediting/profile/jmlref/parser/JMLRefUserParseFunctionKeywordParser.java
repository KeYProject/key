package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;

/**
 * Defines a parse function keyword content parser which can be used to define
 * user keywords.
 * 
 * @author Moritz Lichter
 *
 */
public abstract class JMLRefUserParseFunctionKeywordParser extends
      JMLRefParseFunctionKeywordParser implements
      IUserDefinedKeywordContentDescription {

   @Override
   public String getId() {
      return this.getClass().getName();
   }

   @Override
   public IKeywordParser getKeywordParser() {
      return this;
   }

}
