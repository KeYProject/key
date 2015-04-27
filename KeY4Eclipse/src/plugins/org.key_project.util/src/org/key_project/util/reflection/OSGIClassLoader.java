package org.key_project.util.reflection;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Iterator;
import java.util.Properties;
import java.util.ServiceConfigurationError;
import java.util.Set;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

/**
 * An {@link IClassLoader} implementation for OSGI (Eclipse) plug-ins.
 * <p>
 * In an OSGI (Eclipse) setup has each {@link Bundle} (plug-in) its own {@link ClassLoader}.
 * To access {@link Class}es in a different {@link Bundle} the {@link Bundle} needs
 * to be known to access its {@link ClassLoader}.
 * <p>
 * Instead of searching {@link Class}es in all available {@link Bundle}s only 
 * {@link Bundle} registered via extension point {@value #CLASS_LOADING_BUNDLES_EXTENSION_POINT}
 * are considered for efficiency.
 * @author Martin Hentschel
 */
public class OSGIClassLoader extends JavaApplicationClassLoader {
   /**
    * The name of the extension point which provides the contributiong {@link Bundle}s.
    */
   private static final String CLASS_LOADING_BUNDLES_EXTENSION_POINT = "org.key_project.util.classLoadingBundles";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Class<?> getClassforName(String className) throws ClassNotFoundException {
      return getClassforName(className, "currentBundleIsCheckedByClassforName");
   }
   
   /**
    * Searches the {@link Class} in all contributing bundles and in the current {@link ClassLoader} as fallback.
    * @param className The name of the class.
    * @param configurationAttribute The configuration attribute to check.
    * @return The found {@link Class}.
    * @throws ClassNotFoundException Occurred Exception if {@link Class} was not found.
    */
   protected Class<?> getClassforName(String className, String configurationAttribute) throws ClassNotFoundException {
      // Try to load class from Bundles
      IExtensionRegistry registry = Platform.getExtensionRegistry();
      if (registry != null) {
         IExtensionPoint point = registry.getExtensionPoint(CLASS_LOADING_BUNDLES_EXTENSION_POINT);
         if (point != null) {
            IExtension[] extensions = point.getExtensions();
            for (IExtension extension : extensions) {
               IConfigurationElement[] configElements = extension.getConfigurationElements();
               for (IConfigurationElement configElement : configElements) {
                  try {
                     if (Boolean.valueOf(configElement.getAttribute(configurationAttribute))) {
                        Bundle bundle = Platform.getBundle(extension.getContributor().getName());
                        return bundle.loadClass(className);
                     }
                  }
                  catch (Exception e) {
                     // Class not available, nothing to do.
                  }
               }
            }
         }
      }
      // Try to use default Java class loading if class was not found in Bundles.
      return super.getClassforName(className);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public <S> Iterable<S> loadServices(Class<?> contextClass, Class<S> service) {
      assert contextClass != null;
      assert service != null;
      URL url = contextClass.getClassLoader().getResource("META-INF/services/" + service.getName());
      assert url != null;
      Properties properties = new Properties();
      try (InputStream in = url.openStream()) {
         properties.load(in);
      }
      catch (IOException e) {
         throw new ServiceConfigurationError(service.getName() + ": Can not read configuration-file", e);
      }
      return new ClassNameIterable<S>(service, properties.stringPropertyNames());
   }
   
   /**
    * The {@link Iterable} of {@link OSGIClassLoader#loadServices(Class, Class)}.
    * @author Martin Hentschel
    * @param <S> The service type.
    */
   private class ClassNameIterable<S> implements Iterable<S> {
      /**
       * The requested service.
       */
      private final Class<S> service;

      /**
       * The defined service class names.
       */
      private final Set<String> classNames;

      /**
       * Constructor.
       * @param service The requested service.
       * @param classNames The defined service class names.
       */
      public ClassNameIterable(Class<S> service, Set<String> classNames) {
         this.service = service;
         this.classNames = classNames;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Iterator<S> iterator() {
         return new ServiceIterator<S>(service, classNames.iterator());
      }
   }
   
   /**
    * The {@link Iterator} of {@link ClassNameIterable}.
    * @author Martin Hentschel
    * @param <S> The service type.
    */
   private class ServiceIterator<S> implements Iterator<S> {
      /**
       * The requested service.
       */
      private final Class<S> service;

      /**
       * The underlying {@link Iterator} of class names. 
       */
      private final Iterator<String> classNameIterator;

      /**
       * Constructor.
       * @param service The requested service.
       * @param classNameIterator The underlying {@link Iterator} of class names. 
       */
      public ServiceIterator(Class<S> service, Iterator<String> classNameIterator) {
         this.service = service;
         this.classNameIterator = classNameIterator;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean hasNext() {
         return classNameIterator.hasNext();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public S next() {
         String cn = classNameIterator.next();
         Class<?> c = null;
         try {
            c = getClassforName(cn, "currentBundleIsCheckedByLoadServices");
         }
         catch (ClassNotFoundException x) {
            throw new ServiceConfigurationError(service.getName() + ": " + "Provider " + cn + " not found");
         }
         if (!service.isAssignableFrom(c)) {
            throw new ServiceConfigurationError(service.getName() + ": " + "Provider " + cn + " not a subtype");
         }
         try {
            return service.cast(c.newInstance());
         }
         catch (Throwable t) {
            throw new ServiceConfigurationError(service.getName() + ": " + "Provider " + cn + " could not be instantiated", t);
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void remove() {
         throw new UnsupportedOperationException();
      }
   }
}
