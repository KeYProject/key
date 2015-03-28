package org.key_project.util.reflection;

import java.util.ServiceLoader;

/**
 * Instances of this class allow to access {@link Class}es at
 * runtime in a special application type. 
 * <p>
 * There is no need to work with this interface directly. 
 * The instance to use and all required functionality is
 * provided by the {@link ClassLoaderUtil}.
 * @author Martin Hentschel
 * @see ClassLoaderUtil
 */
public interface IClassLoader {
   /**
    * Returns the {@link Class} for the given class name similar
    * to {@link Class#forName(String)}.
    * @param className The name of the class.
    * @return The {@link Class} instance.
    * @throws ClassNotFoundException Occurred Exception if {@link Class} is not available.
    */
   public Class<?> getClassforName(String className) throws ClassNotFoundException;
   
   /**
    * Loads all configured services similar to {@link ServiceLoader#load(Class)}.
    * @param contextClass The calling {@link Class} which {@link ClassLoader} knows the configuration-file.
    * @param service The requested service.
    * @return An {@link Iterable} with the created service instances.
    */
   public <S> Iterable<S> loadServices(Class<?> contextClass, Class<S> service);
}
