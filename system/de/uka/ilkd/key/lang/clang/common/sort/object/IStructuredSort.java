package de.uka.ilkd.key.lang.clang.common.sort.object;

public interface IStructuredSort extends IInstantiableObjectSort {

        /**
         * Returns structured type's id.
         * @return
         */
        String getId();
        
        /**
         * Returns a map from member ids to member information. Do not modify this map,
         * unless interface implementation allows it.
         * @return
         */        
        HashMapFromStringToMemberInfo getMemberInfoMap();
}