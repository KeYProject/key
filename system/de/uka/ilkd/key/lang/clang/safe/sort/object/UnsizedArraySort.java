package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * Unsized array sort.
 * @author oleg.myrk@gmail.com
 */
public class UnsizedArraySort extends BaseObjectSort {
        
        /**
         * Array's value sort (can be both value and object).
         */
        private final IInstantiableObjectSort elemSort;

        /**
         * Function <code>elem</code> associated with this type instance.
         */
        private ElemFunction elemFunction;
        
        /**
         * Array repository function <code>&lt;lookup&gt;</code> associated with this type instance. 
         */
        private ArrayRepositoryFunction repositoryFunction;
        
        /**
         * Creates array sort with given element sort.
         * @param elemSort
         * @param objectMarkerSort
         * @param arrayMarkerSort
         * @param voidSort
         */
        public UnsizedArraySort(IInstantiableObjectSort elemSort, ObjectMarkerSort objectMarkerSort, ArrayMarkerSort arrayMarkerSort, VoidSort voidSort) {
                super(  formatName(elemSort), 
                        SetAsListOfSort.EMPTY_SET
                                .add(objectMarkerSort)
                                .add(arrayMarkerSort)
                                .add(voidSort));
                this.elemSort = elemSort;
        }
        
        /**
         * Returns unsized array sort's element sort.
         * @return
         */
        public IInstantiableObjectSort getElemSort() {
                return elemSort;
        }
        
        /**
         * Returns function <code>elem</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public ElemFunction getElemFunction() {
                return elemFunction;
        }
        
        /**
         * Returns array repository function <code>&lt;lookup&gt;</code> associated with this type instance.
         * It will be <code>null</code> before {@link #register(SortBuilder)} is called.
         * @return
         */
        public ArrayRepositoryFunction getRepositoryFunction() {
                return repositoryFunction;
        }
        
        /**
         * Registers associated symbols.
         * @param sortBuilder
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
                this.elemFunction = new ElemFunction(this, sortBuilder.getIntSort());
                sortBuilder.getFunctionNS().add(elemFunction);
                this.repositoryFunction = new ArrayRepositoryFunction(this, sortBuilder.getIntSort());
                sortBuilder.getFunctionNS().add(repositoryFunction);                
        }
        
        /**
         * Formats sort's name.
         * @param valueSort
         * @return
         */
        public static Name formatName(IInstantiableObjectSort elemSort) {
                return new Name(elemSort.name() + "[]");
        }
}
