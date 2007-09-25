package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.HashMapFromStringToMemberInfo;
import de.uka.ilkd.key.lang.clang.common.sort.object.IStructuredSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IteratorOfMemberInfo;
import de.uka.ilkd.key.lang.clang.common.sort.object.MemberInfo;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * CDL structured sort.
 * @author oleg.myrk@gmail.com
 */
public abstract class StructuredSort extends InstantiableObjectSort implements IStructuredSort {
        /**
         * Id of the structured type.
         */
        private final String id;
        
        /**
         * Map from member ids to member information. Can be modified before method
         * {@link #register(SortBuilder)} is called.
         */
        private final HashMapFromStringToMemberInfo memberInfoMap = new HashMapFromStringToMemberInfo();
        
        /**
         * A map from member ids to rigid member accessor functions.
         */
        private HashMapFromStringToMemberFunction memberFunctionMap; 
        
        /**
         * Creates structured sort with given sort name and id. Member information
         * can be accessed and modified by the corresponding accessor function.
         * @param id structured type identifier
         * @param name structured type name
         * @param objectMarkerSort
         * @param voidSort
         */
        public StructuredSort(String id, Name name, ObjectMarkerSort objectMarkerSort, VoidSort voidSort) {
                super(  name, 
                        SetAsListOfSort.EMPTY_SET
                                .add(objectMarkerSort)
                                .add(voidSort));
                this.id = id;
        }
        
        /**
         * Returns structured type's id.
         * @return
         */
        public String getId() {
                return id;
        }
        
        /**
         * Tells if the sort has already been registered by calling
         * {@link #register(SortBuilder)}.
         * @return
         */
        public boolean getWasRegistered() {
                return memberFunctionMap != null;
        }
        
        /**
         * Returns a map from member ids to member information. This map can
         * be modified only before {@link #register(SortBuilder)} is called.
         * @return
         */
        public HashMapFromStringToMemberInfo getMemberInfoMap() {
                return memberInfoMap;
        }
        
        /**
         * Returns a map from member ids to rigid member accessor functions associated with this sort instance.
         * This map will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * Do not modify this map. 
         * 
         * @return
         */
        public HashMapFromStringToMemberFunction getMemberFunctionMap() {
                return memberFunctionMap;
        }

        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {      
                super.register(sortBuilder);
                memberFunctionMap = new HashMapFromStringToMemberFunction();
                for(IteratorOfMemberInfo i = memberInfoMap.values(); i.hasNext();) {
                        MemberInfo memberInfo = i.next(); 
                        MemberFunction memberFunction = new MemberFunction(this, memberInfo);
                        memberFunctionMap.put(memberInfo.getId(), memberFunction);
                        sortBuilder.getFunctionNS().add(memberFunction);
                }                
        }
}


