package de.uka.ilkd.key.lang.clang.safe.iface;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.common.iface.IClangPlatform;
import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ArrayMarkerSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ObjectMarkerSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.SizedArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.UnsizedArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.VoidSort;
import de.uka.ilkd.key.lang.clang.safe.sort.value.IntegerSort;
import de.uka.ilkd.key.lang.clang.safe.sort.value.ValueMarkerSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Safe CDL specific platform.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangSafePlatform extends IClangPlatform {
        ValueMarkerSort getSafeValueMarkerSort();
        ObjectMarkerSort getSafeObjectMarkerSort();
        ArrayMarkerSort getSafeArrayMarkerSort();
        
        IntegerSort getSafeIntegerSort(String id);
        VoidSort getSafeVoidSort();
        StructSort getSafeStructSort(String id);
        ScalarSort getSafeScalarSort(Sort valueSort);
        UnsizedArraySort getSafeUnsizedArraySort(IInstantiableObjectSort elemSort);
        SizedArraySort getSafeSizedArraySort(IInstantiableObjectSort elemSort, BigInteger size);
}
