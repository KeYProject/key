package de.uka.ilkd.key.java;

import com.github.javaparser.resolution.types.ResolvedType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class JP2KeYTypeConverter {
    private final Services services;
    public JP2KeYTypeConverter(Services services) {
    this.services=services;
    }

    public KeYJavaType convert(ResolvedType rtype) {
        return null;
    }
}
