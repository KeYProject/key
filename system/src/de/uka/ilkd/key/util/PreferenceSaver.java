// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util;

import java.awt.Component;
import java.awt.Container;
import java.awt.Rectangle;
import java.awt.Window;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;
import javax.swing.AbstractButton;
import javax.swing.JMenu;

import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;

/**
 * A simple utility which stores and loads user manipulatable properties of
 * swing components in the system's preferences.
 * 
 * These properties include:
 * <ul>
 * <li>Position and size of windows</li>
 * <li>Selected tab in a tabbed pane</li>
 * <li>Position of split dividers in a split pane</li>
 * <li>State of JCheckBoxMenuItem (selected or not).</li>
 * </ul>
 * 
 * Only named components (use {@link Component#setName(String)}) have their
 * properties written/read.
 * 
 * New components can be supported by implementing a new Saver to the list
 * {@link #SAVERS}.
 * 
 * @author mattias ulbrich
 */
public class PreferenceSaver {

    /**
     * Every Component class has its own Saver class.
     * 
     * @param <C>
     *            the type of Components to store/read.
     */
    private static interface Saver<C extends Component> {
        Class<C> supportedClass();

        void save(C component, Preferences prefs);

        void load(C component, Preferences prefs);
    }

    /**
     * {@link Saver}s knwon to the system.
     */
    private static Saver<?> SAVERS[] = {
            new WindowSaver(), new SplitPaneSaver(), new TabbedPaneSaver(),
        new AbstractButtonSaver()
    };

    /**
     * get a saver for a component.
     */
    @SuppressWarnings("unchecked")
    private static <C extends Component> Saver<C> getSaver(C component) {
        for (Saver<?> saver : SAVERS) {
            if (saver.supportedClass().isInstance(component)) {
                return (Saver<C>) saver;
            }
        }
        return null;
    }

    /** do the storing/loading from this object */
    private final Preferences prefs;

    /**
     * Create a new instance allowing to store and load UI properties from the
     * user's preferences.
     * 
     * @param prefs
     *            a non-null preference object.
     */
    public PreferenceSaver(Preferences prefs) {
        assert prefs != null;
        this.prefs = prefs;
    }
    
    // JMenu.getComponents() returns an empty array.
    // JMenu.getMenuComponents() has to be used instead.
    private Component[] getChildren(Component component) {
        Component[] children;
        if (component instanceof JMenu) {
            children = ((JMenu) component).getMenuComponents();
        } else {
            children = ((Container) component).getComponents();
        }
        return children;
    }
    
    /**
     * Save the properties of the argument and all its children (in depth).
     * 
     * The preferences are {@linkplain Preferences#flush() flushed} after
     * writing them.
     * 
     * @param component
     *            component to store.
     * 
     * @throws BackingStoreException
     *             possibly thrown by {@link Preferences}.
     */
    public void save(Component component) {
        assert component != null;

        saveComponent(component);
        saveChildren(component);
    }

    private <C extends Component> void saveComponent(C component) {
        String name = component.getName();
        if (name != null) {
            Saver<C> saver = getSaver(component);
            if (saver != null) {
                saver.save(component, prefs);
            }
        }
    }

    private void saveChildren(Component component) {
        if (component instanceof Container) {
            Component[] children = getChildren(component);
            if (children != null) {
                for (Component child : children) {
                    saveComponent(child);
                    saveChildren(child);
                }
            }
        }
    }

    /**
     * Load the properties of the argument and all its children (in depth).
     * 
     * @param component
     *            component to load.
     */
    public void load(Component component) {
        assert component != null;

        loadComponent(component);
        loadChildren(component);
    }

    private <C extends Component> void loadComponent(C component) {
        String name = component.getName();
        if (name != null) {
            Saver<C> saver = getSaver(component);
            if (saver != null) {
                saver.load(component, prefs);
            }
        }
    }

    private void loadChildren(Component component) {
        if (component instanceof Container) {
            Component[] children = getChildren(component);
            if (children != null) {
                for (Component child : children) {
                    load(child);
                }
            }
        }
    }

    /**
     * Windows get their bounding box stored.
     */
    private static class WindowSaver implements Saver<Window> {

        @Override
        public void load(Window component, Preferences prefs) {
            String name = component.getName();
            assert name != null;

            Rectangle bounds = component.getBounds();
            bounds.x = prefs.getInt(name + ".x", bounds.x);
            bounds.y = prefs.getInt(name + ".y", bounds.y);
            bounds.width = prefs.getInt(name + ".width", bounds.width);
            bounds.height = prefs.getInt(name + ".height", bounds.height);
            component.setBounds(bounds);
        }

        @Override
        public void save(Window component, Preferences prefs) {
            String name = component.getName();
            assert name != null;

            Rectangle bounds = component.getBounds();
            prefs.putInt(name + ".x", bounds.x);
            prefs.putInt(name + ".y", bounds.y);
            prefs.putInt(name + ".width", bounds.width);
            prefs.putInt(name + ".height", bounds.height);
        }

        @Override
        public Class<Window> supportedClass() {
            return Window.class;
        }
    }

    /**
     * Splitpanes store the location of the divider.
     */
    private static class SplitPaneSaver implements Saver<JSplitPane> {

        @Override
        public void load(JSplitPane component, Preferences prefs) {
            String name = component.getName();
            assert name != null;

            int splitPoint = component.getDividerLocation();
            component.setDividerLocation(prefs.getInt(
                    name + ".dividerLocation", splitPoint));
        }

        @Override
        public void save(JSplitPane component, Preferences prefs) {
            String name = component.getName();
            assert name != null;

            int splitPoint = component.getDividerLocation();
            prefs.putInt(name + ".dividerLocation", splitPoint);
        }

        @Override
        public Class<JSplitPane> supportedClass() {
            return JSplitPane.class;
        }

    }

    /**
     * tabbed panes store the index of the selected pane.
     */
    private static class TabbedPaneSaver implements Saver<JTabbedPane> {

        @Override
        public void load(JTabbedPane component, Preferences prefs) {
            String name = component.getName();
            assert name != null;

            int index = component.getSelectedIndex();
            int pref = prefs.getInt(name + ".selectedIndex", index);
            component.setSelectedIndex(Math.min(pref,
                    component.getTabCount() - 1));
        }

        @Override
        public void save(JTabbedPane component, Preferences prefs) {
            String name = component.getName();
            assert name != null;

            int index = component.getSelectedIndex();
            prefs.putInt(name + ".selectedIndex", index);
        }

        @Override
        public Class<JTabbedPane> supportedClass() {
            return JTabbedPane.class;
        }

    }

    private static class AbstractButtonSaver implements Saver<AbstractButton> {

        private static String getButtonId(AbstractButton component) {
            return component.getClass().getSimpleName() + "." + component.getName() + ".selected";
        }

        @Override
        public void load(AbstractButton component, Preferences prefs) {
            assert component.getName() != null;
            boolean selected = prefs.getBoolean(getButtonId(component), component.isSelected());
            component.setSelected(selected);
        }

        @Override
        public void save(AbstractButton component, Preferences prefs) {
            assert component.getName() != null;
            boolean selected = component.isSelected();
            prefs.putBoolean(getButtonId(component), selected);
        }

        @Override
        public Class<AbstractButton> supportedClass() {
            return AbstractButton.class;
        }

    }

    public void flush() throws BackingStoreException {
        prefs.flush();
    }
    
}
