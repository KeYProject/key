package de.uka.ilkd.key.gui.ext;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * @author Alexander Weigl
 * @version 1 (07.02.19)
 */
public final class KeYGuiExtensionFacade {
    @SuppressWarnings("todo")
    public static List<KeYPane> getAllPanels() {
        Spliterator<KeYPane> iter = ServiceLoader.load(KeYPane.class).spliterator();
        return StreamSupport.stream(iter, false)
                .sorted(Comparator.comparingInt(KeYPane::priority))
                .collect(Collectors.toList());
    }

    public static <T extends KeYPane> T getPanel(Class<T> clazz) {
        Optional<KeYPane> v = getAllPanels().stream()
                .filter(it -> it.getClass().isAssignableFrom(clazz))
                .findAny();
        return (T) v.orElse(null);
    }
}
