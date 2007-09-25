package de.uka.ilkd.key.lang.clang.common.iface;

import java.math.BigInteger;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.IClangValueSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IArraySort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IStructuredSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IVoidSort;
import de.uka.ilkd.key.lang.clang.common.sort.value.IPointerSort;
import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;
import de.uka.ilkd.key.lang.clang.common.type.IClangObjectType;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.lang.clang.common.type.object.ArrayType;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.clang.common.type.object.VoidType;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * C language platform is a parametrization of C plugin with a particular
 * CDL, which also includes information on possible C implementations.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangPlatform {
        String getCHARId();

        String getUCHARId();

        String getSCHARId();

        String getUSHRTId();

        String getSSHRTId();

        String getUINTId();

        String getSINTId();

        String getULONGId();

        String getSLONGId();

        String getULLONGId();

        String getSLLONGId();

        String getPTRDIFFId();

        String getSIZEId();

        // TODO: add support for extended integers

        IClangValueSort getIntegerSort(String id);

        ArithmeticType getIntegerType(String id);

        KeYJavaType getIntegerTypePair(String id);

        IVoidSort getVoidSort();

        VoidType getVoidType();

        KeYJavaType getVoidTypePair();

        IStructuredSort getStructSort(String id);

        StructType getStructType(String id);

        KeYJavaType getStructTypePair(String id);

        IScalarSort getScalarSort(Sort sort);

        ScalarType getScalarType(IClangValueType type);

        KeYJavaType getScalarTypePair(KeYJavaType typePair);

        IPointerSort getPointerSort(IClangObjectSort sort);

        PointerType getPointerType(IClangObjectType type);

        KeYJavaType getPointerTypePair(KeYJavaType typePair);

        IArraySort getArraySort(IInstantiableObjectSort sort, BigInteger size);

        ArrayType getArrayType(IClangInstantiableObjectType type,
                        BigInteger size);

        KeYJavaType getArrayTypePair(KeYJavaType typePair, BigInteger size);

        /**
         * Promotes C arithmetic integer type if needed. Returns null if
         * promotion is not possible (or not known). Otherwise returns
         * <code>TypePair[]{ null }</code> when promotion is needed and
         * <code>TypePair[]{ T }</code> with promoted type <code>T</code>
         * when needed.
         * 
         * @param type
         * @return
         */
        KeYJavaType[] promoteIntegerTypePair(KeYJavaType type);

        /**
         * Performs usual arithmetic coversions of two arithmetic integer types.
         * Returns <code>null</code> if the conversions are not possible (or
         * not known). Otherwise returns <code>new TypePair[]{ T1, T2 }</code>,
         * where <code>T1</code> and <code>T2</code> are the converted types
         * corresponding to the original types, or <code>null</code> if the
         * conversion of a type is not needed.
         * 
         * @param type1
         * @param type2
         * @return
         */
        KeYJavaType[] usualConversionOfTypePairs(KeYJavaType type1,
                        KeYJavaType type2);
}
