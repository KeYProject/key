package de.uka.ilkd.key.lang.clang.safe.sort.object;

import java.math.BigInteger;

import de.uka.ilkd.key.lang.clang.common.sort.object.IInstantiableObjectSort;
import de.uka.ilkd.key.lang.clang.common.sort.object.IArraySort;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.SetAsListOfSort;

/**
 * CDL sized array sort.
 * @author oleg.myrk@gmail.com
 */
public class SizedArraySort extends InstantiableObjectSort implements IArraySort {
        
        /**
         * Array sort's supertype.
         */
        private final UnsizedArraySort unsizedArraySort;
        
        /**
         * Array sort's size.
         */
        private final BigInteger size;
        
        /**
         * Creates sized array sort with given element sort and size.
         * @param elemSort
         * @param size
         * @param unsizedArraySort
         */
        public SizedArraySort(UnsizedArraySort unsizedArraySort, BigInteger size) {
                super(  formatName(unsizedArraySort.getElemSort(), size), 
                        SetAsListOfSort.EMPTY_SET
                                .add(unsizedArraySort));
                this.unsizedArraySort = unsizedArraySort;
                this.size = size;
        }
        
        /**
         * Returns array sort's supersort.
         * @return
         */
        public UnsizedArraySort getUnsizedArraySort() {
                return unsizedArraySort;
        }
        
        /**
         * Returns array sort's element sort.
         * @return
         */
        public IInstantiableObjectSort getElemSort() {
                return unsizedArraySort.getElemSort();
        }

        
        /**
         * Returns array sort's size.
         * @return
         */
        public BigInteger getSize() {
                return size;
        }

        /**
         * Registers associated symbols.
         * @param sortBuilder 
         */
        public void register(SortBuilder sortBuilder) {
                super.register(sortBuilder);
        }
        
        /**
         * Formats sort's name.
         * @param valueSort
         * @return
         */
        public static Name formatName(IInstantiableObjectSort elemSort, BigInteger size) {
                return new Name(elemSort.name() + "[" + size + "]");
        }
}
