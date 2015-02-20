package org.key_project.jmlediting.core.profile.persistence.internal;

import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.BUNDLE;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CLASS;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CODED_KEYWORD;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.USER_DEFINED_KEYWORD;

import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IUserDefinedKeyword;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public abstract class KeywordPersistence {

   public Element persist(final IKeyword keyword, final Document doc)
         throws ProfilePersistenceException {
      if (keyword instanceof IUserDefinedKeyword) {
         throw new AssertionError("Cannot be persisted yet.");
      }
      else {
         this.validateKeywordToPersist(keyword);
         final Element codedKeywordElem = doc.createElement(CODED_KEYWORD);

         final Bundle keywordBundle = FrameworkUtil.getBundle(keyword
               .getClass());
         if (keywordBundle != null && keywordBundle.getSymbolicName() != null) {
            codedKeywordElem.setAttribute(BUNDLE,
                  keywordBundle.getSymbolicName());
         }
         codedKeywordElem.setAttribute(CLASS, keyword.getClass().getName());

         return codedKeywordElem;
      }
   }

   protected abstract void validateKeywordToPersist(IKeyword keyword)
         throws ProfilePersistenceException;

   protected abstract IKeyword loadKeyword(String className, String bundleName)
         throws ProfilePersistenceException;

   public IKeyword readKeyword(final Element elem)
         throws ProfilePersistenceException {
      final String name = elem.getNodeName();
      if (USER_DEFINED_KEYWORD.equals(name)) {
         throw new AssertionError("Cannot be persisted yet.");
      }
      else if (CODED_KEYWORD.equals(name)) {
         final String keywordClassName = elem.getAttribute(CLASS);
         if ("".equals(keywordClassName)) {
            throw new ProfilePersistenceException(
                  "No keyword class specified for the coded keyword node");
         }
         final String bundleId = elem.getAttribute(BUNDLE);
         return this.loadKeyword(keywordClassName, bundleId);
      }
      else {
         throw new ProfilePersistenceException(
               "Got illegal profile element with name \"" + name + "\"");
      }
   }

}
