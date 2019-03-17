package org.key_project.util.reflection;

import java.util.ServiceLoader;

/**
 * This class provides utility methods to load classes at runtime
 * which works in all supported application types:
 * <ul>
 *    <li>Java Application</li>
 *    <li>OSGI (Eclipse)</li>
 * </ul>
 * <p>
 * The Java reflection framework allows to load classes at runtime
 * for instance via {@link Class#forName(String)}. In a configuration-file
 * configured classes can also be instantiated via the {@link ServiceLoader}.
 * But both approaches work only, if the {@link Class} to work with is known
 * by the current {@link ClassLoader}. This is no problem in a normal Java Application
 * since all classes are managed by the same {@link ClassLoader}. But in an
 * OSGI setup like Eclipse, each component (plug-in) has its own {@link ClassLoader}.
 * The consequence is that the reflection framework can only work with classes
 * in the same component as they are only known by the current {@link ClassLoader}.
 * <p>
 * To achieve the same behavior in all supported types provides this class utility
 * methods which should be used instead:
 * <ul>
 *    <li>{@link #getClassforName(String)} instead of {@link Class#forName(String)}</li>
 *    <li>{@link #loadServices(Class, Class) instead of {@link ServiceLoader#load(Class)}</li>
 * </ul>
 * <p>
 * The application specific behavior is implemented in {@link IClassLoader} instances.
 * The used instance is accessible via {@link #getClassLoader()} which is by default
 * the {@link JavaApplicationClassLoader}. In an OSGI (Eclipse) setup the instance
 * is replaced via {@link #setClassLoader(IClassLoader)} with an {@code OSGIClassLoader}
 * instance.
 * @author Martin Hentschel
 * @see IClassLoader
 * @see JavaApplicationClassLoader
 */
public class ClassLoaderUtil {
   /**
    * The {@link IClassLoader} instance to use.
    */
   private static IClassLoader classLoader = new JavaApplicationClassLoader();

   /**
    * Returns the used {@link IClassLoader}.
    * @return The used {@link IClassLoader}.
    */
   public static IClassLoader getClassLoader() {
      return classLoader;
   }
   
   /**
    * Sets the {@link IClassLoader} instance to use.
    * @param classLoader The {@link IClassLoader} instance to use.
    */
   public static void setClassLoader(IClassLoader classLoader) {
      ClassLoaderUtil.classLoader = classLoader;
   }

   /**
    * Returns the {@link Class} for the given class name similar
    * to {@link Class#forName(String)} but with same behavior in all
    * supported application types.
    * @param className The name of the class.
    * @return The {@link Class} instance.
    * @throws ClassNotFoundException Occurred Exception if {@link Class} is not available.
    */
   public static Class<?> getClassforName(String className) throws ClassNotFoundException {
      return classLoader.getClassforName(className);
   }
   
   /**
    * Loads all configured services similar to {@link ServiceLoader#load(Class)}
    * but with same behavior in all supported application types.
    * @param service The requested service.
    * @return An {@link Iterable} with the created service instances.
    */
   public static <S> Iterable<S> loadServices(Class<S> service) {
      return classLoader.loadServices(service, service);
   }
   
   /**
    * Loads all configured services similar to {@link ServiceLoader#load(Class)}
    * but with same behavior in all supported application types.
    * @param contextClass The calling {@link Class} which {@link ClassLoader} knows the configuration-file.
    * @param service The requested service.
    * @return An {@link Iterable} with the created service instances.
    */
   public static <S> Iterable<S> loadServices(Class<?> contextClass, Class<S> service) {
      return classLoader.loadServices(contextClass, service);
   }
}
