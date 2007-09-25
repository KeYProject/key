package de.uka.ilkd.key.lang.clang.safe.sort;

import java.util.Map;

import de.uka.ilkd.key.lang.clang.common.type.IntegerTypeUtil;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Standard C sorts.
 * 
 * @author oleg.myrk@gmail.com
 */
public class IntegerSortUtil {
        public final static String CHAR_SORT_ID = "CHAR";
        public final static String SCHAR_SORT_ID = "SCHAR";
        public final static String UCHAR_SORT_ID = "UCHAR";
        public final static String SSHRT_SORT_ID = "SSHRT";
        public final static String USHRT_SORT_ID = "USHRT";
        public final static String SINT_SORT_ID = "SINT";
        public final static String UINT_SORT_ID = "UINT";
        public final static String SLONG_SORT_ID = "SLONG";
        public final static String ULONG_SORT_ID = "ULONG";
        public final static String SLLONG_SORT_ID = "SLLONG";
        public final static String ULLONG_SORT_ID = "ULLONG";

        /**
         * Registers standard C sorts in the sort builder and a map from type IDs to sorts.
         */
        public static void registerStandardSorts(SortBuilder sortBuilder, Map typeIdSortMap) {
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.CHAR_TYPE_ID,
                                IntegerSortUtil.CHAR_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.SCHAR_TYPE_ID,
                                IntegerSortUtil.SCHAR_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.UCHAR_TYPE_ID,
                                IntegerSortUtil.UCHAR_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.SSHRT_TYPE_ID,
                                IntegerSortUtil.SSHRT_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.USHRT_TYPE_ID,
                                IntegerSortUtil.USHRT_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.SINT_TYPE_ID,
                                IntegerSortUtil.SINT_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.UINT_TYPE_ID,
                                IntegerSortUtil.UINT_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.SLONG_TYPE_ID,
                                IntegerSortUtil.SLONG_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.ULONG_TYPE_ID,
                                IntegerSortUtil.ULONG_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.SLLONG_TYPE_ID,
                                IntegerSortUtil.SLLONG_SORT_ID);
                registerSort(sortBuilder, typeIdSortMap,
                                IntegerTypeUtil.ULLONG_TYPE_ID,
                                IntegerSortUtil.ULLONG_SORT_ID);
        }
        
        /**
         * Registers a C sorts with given ID in the sort builder and a map from type IDs to sorts.
         */
        public static void registerSort(SortBuilder sortBuilder, Map integerTypeIdSortMap, 
                        String typeId, String sortId) {
                Sort sort = sortBuilder.getIntegerSort(sortId);
                if (sort == null)
                        sort = sortBuilder.registerIntegerSort(sortId);
                integerTypeIdSortMap.put(typeId, sort);
        }        
}
