package de.uka.ilkd.key.lang.clang.common.util;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.common.sort.value.IPointerSort;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Utilities for type pairs.
 * 
 * @author oleg.myrk@gmail.com
 */
public class TypePairUtil {
        static public KeYJavaType extractFromScalarType(KeYJavaType pair) {
                Type type = pair.getJavaType();
                Sort sort = pair.getSort();

                if (!(type instanceof ScalarType && sort instanceof IScalarSort))
                        return null;

                Type valueType = ((ScalarType) type).getValueType();
                Sort valueSort = ((IScalarSort) sort).getValueSort();

                return new KeYJavaType(valueType, valueSort);
        }

        static public KeYJavaType extractFromPointerType(KeYJavaType pair) {
                Type type = pair.getJavaType();
                Sort sort = pair.getSort();

                if (!(type instanceof PointerType)
                                || !(sort instanceof IPointerSort))
                        return null;

                Type targetType = ((PointerType) type).getTargetType();
                Sort targetSort = ((IPointerSort) sort).getTargetSort();

                return new KeYJavaType(targetType, targetSort);
        }
        
        // TODO: extractFromArrayType
}
