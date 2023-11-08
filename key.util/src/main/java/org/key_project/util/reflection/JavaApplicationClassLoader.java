/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.reflection;

import java.util.ServiceLoader;

/**
 * An {@link IClassLoader} implementation for Java Applications.
 * <p>
 * In a Java Application all {@link Class}es are loaded by the same {@link ClassLoader} and thus the
 * Java API can be used directly to realize the functionality.
 *
 * @author Martin Hentschel
 */
public class JavaApplicationClassLoader implements IClassLoader {
    /**
     * {@inheritDoc}
     */
    @Override
    public Class<?> getClassforName(String className) throws ClassNotFoundException {
        return Class.forName(className);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <S> Iterable<S> loadServices(Class<?> contextClass, Class<S> service) {
        return ServiceLoader.load(service);
    }
}
