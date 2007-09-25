package de.uka.ilkd.key.lang.clang.safe.services;

import java.math.BigInteger;
import java.util.Map;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.iface.BaseClangPlatform;
import de.uka.ilkd.key.lang.clang.common.sort.IClangObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.IClangValueSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IArraySort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IScalarSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IStructuredSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IVoidSort;
import de.uka.ilkd.key.lang.clang.common.sort.value.IPointerSort;
import de.uka.ilkd.key.lang.clang.common.type.IntegerTypeUtil;
import de.uka.ilkd.key.lang.clang.common.type.TypeBuilder;
import de.uka.ilkd.key.lang.clang.safe.iface.IClangSafePlatform;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
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
 * Safe CDL platform implementation.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ClangSafePlatform extends BaseClangPlatform implements IClangSafePlatform {
        private SortBuilder sortBuilder;

        private Map integerTypeIdSortMap;

        public ClangSafePlatform(TypeBuilder typeBuilder, SortBuilder sortBuilder,
                        Map integerTypeIdSortMap) {
                super(typeBuilder);
                this.sortBuilder = sortBuilder;
                this.integerTypeIdSortMap = integerTypeIdSortMap;
        }

        public String getCHARId() {
                return IntegerTypeUtil.CHAR_TYPE_ID;
        }

        public String getSCHARId() {
                return IntegerTypeUtil.SCHAR_TYPE_ID;
        }

        public String getUCHARId() {
                return IntegerTypeUtil.UCHAR_TYPE_ID;
        }

        public String getSSHRTId() {
                return IntegerTypeUtil.SSHRT_TYPE_ID;
        }

        public String getUSHRTId() {
                return IntegerTypeUtil.USHRT_TYPE_ID;
        }

        public String getSINTId() {
                return IntegerTypeUtil.SINT_TYPE_ID;
        }

        public String getUINTId() {
                return IntegerTypeUtil.UINT_TYPE_ID;
        }

        public String getSLONGId() {
                return IntegerTypeUtil.SLONG_TYPE_ID;
        }

        public String getULONGId() {
                return IntegerTypeUtil.ULONG_TYPE_ID;
        }

        public String getSLLONGId() {
                return IntegerTypeUtil.SLLONG_TYPE_ID;
        }

        public String getULLONGId() {
                return IntegerTypeUtil.ULLONG_TYPE_ID;
        }

        public String getPTRDIFFId() {
                // TODO
                throw new RuntimeException("Not implemented yet!");
        }

        public String getSIZEId() {
                // TODO
                throw new RuntimeException("Not implemented yet!");
        }

        public IClangValueSort getIntegerSort(String id) {
                return (IClangValueSort) integerTypeIdSortMap.get(id);
        }

        public IVoidSort getVoidSort() {
                return sortBuilder.getVoidSort();
        }

        public IStructuredSort getStructSort(String id) {
                return sortBuilder.getStructSort(id);
        }

        public IScalarSort getScalarSort(Sort sort) {
                return sortBuilder.getScalarSort(sort);
        }

        public IPointerSort getPointerSort(IClangObjectSort sort) {
                return (IPointerSort) sort;
        }

        public IArraySort getArraySort(IInstantiableObjectSort sort,
                        BigInteger size) {
                return sortBuilder.getSizedArraySort(sort, size);
        }

        public KeYJavaType[] promoteIntegerTypePair(KeYJavaType type) {
                return null;
        }

        public KeYJavaType[] usualConversionOfTypePairs(KeYJavaType type1,
                        KeYJavaType type2) {
                return null;
        }

        public ValueMarkerSort getSafeValueMarkerSort() {
                return sortBuilder.getValueMarkerSort();
        }

        public ObjectMarkerSort getSafeObjectMarkerSort() {
                return sortBuilder.getObjectMarkerSort();
        }

        public ArrayMarkerSort getSafeArrayMarkerSort() {
                return sortBuilder.getArrayMarkerSort();
        }

        public IntegerSort getSafeIntegerSort(String id) {
                return (IntegerSort) getIntegerSort(id);
        }

        public VoidSort getSafeVoidSort() {
                return (VoidSort) getVoidSort();
        }

        public StructSort getSafeStructSort(String id) {
                return (StructSort) getStructSort(id);
        }

        public ScalarSort getSafeScalarSort(Sort valueSort) {
                return (ScalarSort) getScalarSort(valueSort);
        }

        public UnsizedArraySort getSafeUnsizedArraySort(
                        IInstantiableObjectSort elemSort) {
                return (UnsizedArraySort) sortBuilder
                                .getUnsizedArraySort(elemSort);
        }

        public SizedArraySort getSafeSizedArraySort(
                        IInstantiableObjectSort elemSort, BigInteger size) {
                return (SizedArraySort) getArraySort(elemSort, size);
        }
}
