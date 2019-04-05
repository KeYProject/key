package de.uka.ilkd.key.gui.lookup;

import de.uka.ilkd.key.java.Services;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (15.03.19)
 */
public class Lookup {
    private final Lookup parent;
    private final HashMap<Class<?>, LinkedList<?>> serviceMap = new HashMap<>();
    private final List<Lookup> children = new ArrayList<>();
    private HashMap<Class<?>, List<LookupListener>> propertyListener = new HashMap<>();

    public Lookup() {
        this(null);
    }

    public Lookup(Lookup parent) {
        this.parent = parent;
        if (parent != null)
            parent.children.add(this);
    }

    public static Lookup fromServices(Services services) {
        Lookup lookup = new Lookup();
        lookup.register(services.getJavaInfo());
        lookup.register(services.getJavaModel());
        lookup.register(services.getProfile());
        lookup.register(services.getProof());
        lookup.register(services.getNamespaces());
        lookup.register(services.getTermBuilder());
        lookup.register(services.getNameRecorder());
        lookup.register(services.getVariableNamer());
        return lookup;
    }

    private void register(Object o) {
        register(o, o.getClass());
    }

    @SuppressWarnings("unchecked")
    private <T> List<T> getList(Class<T> service) {
        return (List<T>) serviceMap.computeIfAbsent(service, (k -> new LinkedList<>()));
    }

    public <T> T get(Class<T> service) {
        List<? extends T> t = getList(service);
        if (t.isEmpty()) {
            if (parent != null) return parent.get(service);
            else throw new IllegalStateException("Service $service not registered");
        } else {
            return t.get(0);
        }
    }

    @SuppressWarnings("unchecked")
    public <T> void register(Object obj, Class<T> service) {
        List<T> list = getList(service);
        final T o = (T) obj;
        list.add(0, o);
        firePropertyChange(service);
    }

    public <T> void deregister(T obj, Class<T> service) {
        boolean b = getList(service).remove(obj);
        if (b) firePropertyChange(service);
        if (parent != null) parent.deregister(obj, service);
    }

    public <T> List<T> getAll(Class<T> service) {
        ArrayList<T> t = new ArrayList<>(getList(service));
        if (parent != null) {
            t.addAll(parent.getAll(service));
        }
        return t;
    }

    public void dispose() {
        if (parent != null) parent.children.remove(this);
    }

    public <T> List<LookupListener> getListeners(Class<?> name) {
        return propertyListener.computeIfAbsent(name, a -> new LinkedList<>());
    }

    public void addChangeListener(LookupListener listener) {
        addChangeListener(ALL.class, listener);
    }

    public <T> void addChangeListener(Class<T> name, LookupListener listener) {
        getListeners(name).add(listener);
    }

    public <T> void removeChangeListener(Class<?> name, LookupListener listener) {
        getListeners(name).remove(listener);
    }

    public void removeChangeListener(LookupListener listener) {
        removeChangeListener(ALL.class, listener);
    }

    public void firePropertyChange(Class<?> name) {
        getListeners(name).forEach(it -> it.update(name));
        children.forEach(it -> it.firePropertyChange(name));
        getListeners(ALL.class).forEach(it -> it.update(name));
        children.forEach(it -> it.firePropertyChange(ALL.class));
    }

    private static class ALL {
    }
}
