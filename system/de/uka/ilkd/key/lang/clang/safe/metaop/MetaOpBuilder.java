package de.uka.ilkd.key.lang.clang.safe.metaop;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryArrayRepositorySizeMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryIsArrayElemMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryIsRealObjMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryIsRootObjMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryIsStructMemberMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryIsValidObjMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryObjAliasedMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryObjContainsMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryObjEqMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryObjParentIdxMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryObjParentMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryRemoveObjAccessorMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryRootObjLookupIdxMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TryRootObjMetaOp;
import de.uka.ilkd.key.lang.clang.safe.metaop.heap.TrySizedArraySizeMetaOp;
import de.uka.ilkd.key.lang.common.metaop.BaseMetaOp;

/**
 * Meta operation builder.
 * @author oleg.myrk@gmail.com
 */
public class MetaOpBuilder {
        
        /**
         * Builds a map from meta operation names to the meta operations. 
         * @return
         */
        public static Map buildMap() {
                Map map = new HashMap();
                
                put(map, new InstanceMetaOp());
                put(map, new CastMetaOp());
                put(map, new UnsizedArraySortMetaOp());
                put(map, new AtomicUpdateMetaOp());
                put(map, new AnonymousUpdateMetaOp());                
                put(map, new IntegerMinMetaOp());
                put(map, new IntegerMaxMetaOp());
                put(map, new IntegerFromIntMetaOp());
                put(map, new IntegerToIntMetaOp());
                put(map, new ValueAccessMetaOp());
                put(map, new MemberAccessMetaOp());
                put(map, new ElemAccessMetaOp());
                put(map, new RepositoryAccessMetaOp());
                put(map, new ArrayRepositoryAccessMetaOp());
                put(map, new IsValidValueMetaOp());
                put(map, new DeepIsValidValueMetaOp());
                put(map, new DeepUpdateMetaOp());
                put(map, new DivMetaOp());
                put(map, new ModMetaOp());
                
                // Heap operations
                put(map, new TryObjEqMetaOp());
                put(map, new TrySizedArraySizeMetaOp());
                put(map, new TryArrayRepositorySizeMetaOp());
                put(map, new TryIsValidObjMetaOp());
                put(map, new TryIsRealObjMetaOp());
                put(map, new TryRemoveObjAccessorMetaOp());
                put(map, new TryRootObjMetaOp());
                put(map, new TryRootObjLookupIdxMetaOp());                
                put(map, new TryObjContainsMetaOp());
                put(map, new TryObjAliasedMetaOp());
                put(map, new TryIsRootObjMetaOp());                
                put(map, new TryIsStructMemberMetaOp());
                put(map, new TryIsArrayElemMetaOp());
                put(map, new TryObjParentMetaOp());
                put(map, new TryObjParentIdxMetaOp());
                
                return map;
        }
        
        private static void put(Map map, BaseMetaOp metaop) {
                map.put(metaop.name(), metaop);
        }
}
