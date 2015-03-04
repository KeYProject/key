package org.key_project.jmlediting.core.profile.persistence.internal;

import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.BUNDLE;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CLASS;
import static org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence.CLASS_REFERENCE;

import org.eclipse.core.runtime.Platform;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class ClassReferencePersistence {

   public Element persistClassReference(final Class<?> classToPersist,
         final Document doc) {
      final Element classRefElement = doc.createElement(CLASS_REFERENCE);
      final Bundle bundle = FrameworkUtil.getBundle(classToPersist);
      if (bundle != null && bundle.getSymbolicName() != null) {
         classRefElement.setAttribute(BUNDLE, bundle.getSymbolicName());
      }
      classRefElement.setAttribute(CLASS, classToPersist.getName());
      return classRefElement;
   }

   public <T> Class<? extends T> loadClassReference(final Element classElement,
         final Class<T> superClass) throws ProfilePersistenceException {
      if (!(classElement.getNodeName().equals(CLASS_REFERENCE))) {
         throw new ProfilePersistenceException("Unable tag for class reference");
      }
      final String className = classElement.getAttribute(CLASS);
      if ("".equals(className)) {
         throw new ProfilePersistenceException(
               "No keyword class specified for the coded keyword node");
      }
      final String bundleId = classElement.getAttribute(BUNDLE);
      Class<?> loadedClass;
      try {

         if (!"".equals(bundleId)) {
            loadedClass = Platform.getBundle(bundleId).loadClass(className);
         }
         else {
            loadedClass = Class.forName(className);
         }

         if (!superClass.isAssignableFrom(loadedClass)) {
            throw new ProfilePersistenceException(
                  "Loaded class is not a subclass of " + superClass.getName());
         }
         return (Class<? extends T>) loadedClass;
      }
      catch (final ClassNotFoundException e) {
         throw new ProfilePersistenceException("Unable to load class", e);
      }
   }

}
