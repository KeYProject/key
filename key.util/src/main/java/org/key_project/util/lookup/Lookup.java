/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.lookup;

import java.lang.ref.WeakReference;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

import org.checkerframework.checker.initialization.qual.Initialized;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class handles the management of services and implementations.
 * <p>
 * This class is a flexible alternative for a mediator. You can register and deregister
 * implementation for services. And also you can lookup them up. Multiple implementations are
 * possible; also notification on service change.
 * <p>
 * {@link Lookup} can be arranged hierarchical, incl. support for notification.
 *
 * @author Alexander Weigl
 * @version 1 (15.03.19)
 */
@NullMarked
public class Lookup {
    public static final Lookup DEFAULT = new Lookup();

    private final @Nullable Lookup parent;

    /**
     * Registered services. The first service in the list is the default.
     */
    private final HashMap<Class<?>, LinkedList<?>> serviceMap = new HashMap<>();

    /**
     *
     */
    private final List<WeakReference<Lookup>> children = new ArrayList<>();

    /**
     * Listeners, that are called on a change. All.class is the key for non specified types.
     */
    private final HashMap<Class<?>, List<LookupListener>> propertyListener = new HashMap<>();

    public Lookup() {
        this(null);
    }

    public Lookup(@Nullable Lookup parent) {
        this.parent = parent;
        if (parent != null) {
            @SuppressWarnings("nullness") // WeakReference to this
            @Initialized
            WeakReference<Lookup> weakthis = new WeakReference<>(this);
            parent.children.add(weakthis);
        }
    }

    /*
     * public static Lookup fromServices(Services services) { Lookup lookup = new Lookup();
     * lookup.register(services.getJavaInfo()); lookup.register(services.getJavaModel());
     * lookup.register(services.getProfile()); lookup.register(services.getProof());
     * lookup.register(services.getNamespaces()); lookup.register(services.getTermBuilder());
     * lookup.register(services.getNameRecorder()); lookup.register(services.getVariableNamer());
     * return lookup; }
     */

    /**
     * Get all registered implementations for the given service class.
     *
     * @param service
     * @param <T>
     * @return
     */
    public <T> Collection<T> lookupAll(Class<T> service) {
        ArrayList<T> t = new ArrayList<>(getList(service));
        if (parent != null) {
            t.addAll(parent.lookupAll(service));
        }
        return t;
    }

    /**
     * Get the current default implementation of the given service.
     *
     * @param service
     * @param <T>
     * @return
     */
    public <T extends @Nullable Object> T get(Class<T> service) {
        List<? extends T> t = getList(service);
        if (t.isEmpty()) {
            if (parent != null) {
                return parent.get(service);
            } else {
                throw new IllegalStateException("Service \"" + service + "\" not registered");
            }
        } else {
            return t.get(0);
        }
    }

    /**
     * Register
     *
     * @param obj
     * @param service
     * @param <T>
     */
    public <T> void register(T obj, Class<T> service) {
        List<T> list = getList(service);
        list.add(0, obj);
        firePropertyChange(service);
    }

    public <T> void deregister(T obj, Class<T> service) {
        boolean b = getList(service).remove(obj);
        if (b) {
            firePropertyChange(service);
        }
        if (parent != null) {
            parent.deregister(obj, service);
        }
    }

    public <T> void deregister(Class<T> service) {
        getList(service).clear();
        firePropertyChange(service);
        if (parent != null) {
            parent.deregister(service);
        }
    }


    public void dispose() {
        if (parent != null) {
            parent.children.remove(this);
        }
    }

    public List<LookupListener> getListeners(Class<?> name) {
        return propertyListener.computeIfAbsent(name, a -> new LinkedList<>());
    }

    public void addChangeListener(LookupListener listener) {
        addChangeListener(ALL.class, listener);
    }

    public void addChangeListener(Class<?> name, LookupListener listener) {
        getListeners(name).add(listener);
    }

    public void removeChangeListener(Class<?> name, LookupListener listener) {
        getListeners(name).remove(listener);
    }

    public void removeChangeListener(LookupListener listener) {
        removeChangeListener(ALL.class, listener);
    }

    protected void firePropertyChange(Class<?> name) {
        getListeners(name).forEach(it -> it.update(name, this));
        children.forEach(it -> {
            Lookup child = it.get();
            if (child != null) {
                child.firePropertyChange(name);
            }
        });
        getListeners(ALL.class).forEach(it -> it.update(name, this));
        children.forEach(it -> {
            Lookup child = it.get();
            if (child != null) {
                child.firePropertyChange(ALL.class);
            }
        });
    }


    @SuppressWarnings("unchecked")
    public <T> void register(T o) {
        register(o, (Class<T>) o.getClass());
    }

    @SuppressWarnings("unchecked")
    private <T extends @Nullable Object> List<T> getList(Class<T> service) {
        return (List<T>) serviceMap.computeIfAbsent(service, (k -> new LinkedList<>()));
    }


    /**
     * Creates an instance of the given class by calling a suitable {@link Inject} constructor.
     *
     * @param clazz
     * @param <T>
     * @return
     * @throws InjectionException if non suitable constructors could be found.
     */
    @SuppressWarnings({ "unchecked",
        "keyfor", "nullness", // KeyFor and type variable bounds
    })
    public <T> @Nullable T createInstance(Class<T> clazz) throws InjectionException {
        for (Constructor<?> ctor : clazz.getConstructors()) {
            if (ctor.getAnnotation(Inject.class) != null) {
                T instance = (T) tryToInject(ctor);
                if (instance != null) {
                    return instance;
                }
            }
        }
        return null;
    }

    /**
     * @param ctor
     * @param <T>
     * @return
     * @throws InjectionException
     */
    protected <T> @Nullable T tryToInject(Constructor<T> ctor) throws InjectionException {
        List<?> services =
            Arrays.stream(ctor.getParameterTypes()).map(this::get).toList();

        if (services.stream().allMatch(Objects::nonNull)) {
            try {
                @SuppressWarnings("nullness") // connection to allMatch lost
                T res = ctor.newInstance(services.toArray());
                return res;
            } catch (InstantiationException | IllegalAccessException
                    | InvocationTargetException e) {
                throw new InjectionException(e);
            }
        }
        return null;
    }

    /**
     * Injects all known service implementation in the given instance.
     * <p>
     * This method searchs for methods single argument methods, that are annotated with
     * {@link Inject}, and calls it with the service implementation.
     *
     * @param instance arbitrary non-null method
     * @throws InjectionException is thrown iff a service is unknown but needed for an
     *         {@link Inject} method.
     */
    public void inject(Object instance) throws InjectionException {
        Class<?> clazz = instance.getClass();
        for (Method setter : clazz.getMethods()) {
            if (setter.getAnnotation(Inject.class) != null) {
                inject(instance, setter);
            }
        }
    }

    /**
     * @param instance
     * @param setter
     * @throws InjectionException
     */
    protected void inject(Object instance, Method setter) throws InjectionException {
        if (setter.getParameterCount() != 1) {
            throw new IllegalStateException();
        }

        Class<?> pClazz = setter.getParameters()[0].getType();
        Object o = get(pClazz);
        if (o == null) {
            throw new IllegalStateException("Implementation for X not registered.");
        }
        try {
            setter.invoke(instance, o);
        } catch (IllegalAccessException | InvocationTargetException e) {
            throw new InjectionException(e);
        }
    }

    private static class ALL {
    }
}
